#![no_std]
#![feature(abi_avr_interrupt)]

use core::pin::Pin;
use core::task::{Context, Poll, Waker};
use avr_hal_generic::usart::Baudrate;
use embedded_io_async::ErrorType;
mod ringbuffer;


use {
    paste,
};


/// Internal trait for low-level USART peripherals.
///
/// This trait defines the common interface for all USART peripheral variants.  It is used as an
/// intermediate abstraction ontop of which the [`UsartWrite`] API is built.  **Prefer using the
/// [`UsartWrite`] API instead of this trait.**
pub trait UsartOps2: Unpin {
    // type RX;
    // type TX;

    fn raw_baudrate<CLOCK>(&mut self, baudrate: Baudrate<CLOCK>);
    fn raw_write_enable(&mut self, enable: bool);
    fn raw_write_init(&mut self);
    fn raw_write(&mut self, buffer: &[u8]) -> usize;

    fn raw_write_waker(&mut self, waker: Option<Waker>);
    fn raw_write_done(&mut self) -> bool;

    fn raw_write_flush(&mut self);
    fn raw_write_stop(&mut self);

    fn raw_write_enabled(&mut self) -> bool;
    
    
    

    fn raw_read_enable(&mut self, enable: bool);
    fn raw_read_init(&mut self);
    fn raw_read(&mut self, buffer: &mut [u8]) -> usize;
    fn raw_read_overflow(&mut self) -> bool;

    fn raw_read_waker(&mut self, waker: Option<Waker>);
    fn raw_read_listen(&mut self, listen: bool);

    fn raw_read_enabled(&mut self) -> bool;
}

#[allow(dead_code)]
pub struct UsartRead<RAW: UsartOps2> {
    p: RAW
}
impl<RAW: UsartOps2> UsartRead<RAW> {
    fn new(mut usart: RAW) -> Self {
        usart.raw_read_init();
        usart.raw_read_listen(true);
        Self {
            p: usart
        }
    }

    pub fn listen(&mut self, listen: bool) {
        self.p.raw_read_listen(listen);
    }
}

impl<RAW: UsartOps2> Drop for UsartRead<RAW> {
    fn drop(&mut self) {
        self.p.raw_read_listen(false);
        self.p.raw_read_enable(false);
    }
}

/// error indicating read buffer is full so bytes has dropped
/// you should increase buffer size or read more often
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct ReadOverflowError;

impl embedded_io_async::Error for ReadOverflowError {
    fn kind(&self) -> ErrorKind {
        ErrorKind::Other
    }
}

impl<RAW: UsartOps2> ErrorType for UsartRead<RAW> { type Error = ReadOverflowError; }

impl<RAW: UsartOps2> embedded_io_async::Read for UsartRead<RAW> {
    async fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        if buf.len() == 0 {
            return Ok(0);
        }
        if self.p.raw_read_overflow() {
            return Err(ReadOverflowError);
        }
        Ok((AsyncRead {
            raw: &mut self.p,
            buffer: buf
        }).await)
    }
}

struct AsyncRead<'a, RAW: UsartOps2> {
    raw: &'a mut RAW,
    buffer: &'a mut [u8]
}

impl<RAW: UsartOps2> core::future::Future for AsyncRead<'_, RAW> {
    type Output = usize;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.raw.raw_read_waker(Some(cx.waker().clone()));
        let buf: &mut [u8] = unsafe {core::ptr::read(&self.buffer)};
        let read = self.raw.raw_read(buf);
        if read != 0 {
            Poll::Ready(read)
        } else {
            Poll::Pending
        }
    }
}

#[allow(dead_code)]
pub struct UsartWrite<RAW: UsartOps2> {
    p: RAW,
    //tx: RAW::TX
}

impl<RAW: UsartOps2> UsartWrite<RAW> {
    fn new(mut usart: RAW, /*tx: RAW::TX*/) -> Self {
        usart.raw_write_init();
        Self {
            p: usart,
            //tx
        }
    }
}

impl<RAW: UsartOps2> Drop for UsartWrite<RAW> {
    fn drop(&mut self) {
        self.p.raw_write_stop();
        self.p.raw_write_enable(false);
    }
}

impl<RAW: UsartOps2> ErrorType for UsartWrite<RAW> { type Error = Infallible; }

impl<RAW: UsartOps2> embedded_io_async::Write for UsartWrite<RAW> {
    #[inline(always)]
    async fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        if buf.len() == 0 {
            return Ok(0);
        }
        Ok((AsyncWrite {
            p: unsafe { core::ptr::read(&self.p) },
            buffer: buf
        }).await)
    }

    async fn flush(&mut self) -> Result<(), Self::Error> {
        Ok((AsyncFlush {
            p: &mut self.p,
        }).await)
    }
}

struct AsyncWrite<'a, RAW: UsartOps2> {
    p: RAW,
    buffer: &'a [u8]
}


impl<RAW: UsartOps2> core::future::Future for AsyncWrite<'_, RAW> {
    type Output = usize;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.p.raw_write_waker(Some(cx.waker().clone()));
        let buffer = self.buffer;
        let wrote = self.p.raw_write(buffer);
        if wrote != 0 {
            Poll::Ready(wrote)
        } else {
            Poll::Pending
        }
    }
}

struct AsyncFlush<'a, RAW: UsartOps2> {
    p: &'a mut RAW
}

impl<RAW: UsartOps2> core::future::Future for AsyncFlush<'_, RAW> {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.p.raw_write_done() {
            Poll::Ready(())
        } else {
            self.p.raw_write_waker(Some(cx.waker().clone()));
            self.p.raw_write_flush();
            Poll::Pending
        }
    }
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UsartNotClosedError;

use core::convert::Infallible;
use embedded_io::ErrorKind;
use portable_atomic::AtomicU8;

/// pack in single byte to reduce memory footprint
static mut USART_FLAG: AtomicU8 = AtomicU8::new(0);

pub struct UsartDriver<RAW: UsartOps2> {
    raw: RAW
}

impl<RAW: UsartOps2> UsartDriver<RAW> {
    pub fn new<CLOCK>(mut raw: RAW, baudrate: Baudrate<CLOCK>) -> Self {
        raw.raw_baudrate(baudrate);
        raw.raw_write_enable(false);
        Self {
            raw
        }
    }
    pub fn baudrate<CLOCK>(&mut self, baudrate: Baudrate<CLOCK>) -> Result<(), UsartNotClosedError> {
        if self.raw.raw_read_enabled() || self.raw.raw_write_enabled() {
            Err(UsartNotClosedError)
        } else {
            self.raw.raw_baudrate(baudrate);
            Ok(())
        }
    }

    pub fn try_into_inner(mut self) -> Result<RAW, Self> {
        if self.raw.raw_read_enabled() || self.raw.raw_write_enabled() {
            Err(self)
        } else {
            Ok(self.raw)
        }
    }

    pub fn write(&mut self, /*tx: RAW::TX*/) -> Option<UsartWrite<RAW>> {
        if self.raw.raw_write_enabled() {
            None
        } else {
            Some(UsartWrite::new(unsafe { core::ptr::read(&self.raw) }))
        }
    }

    pub fn read(&mut self) -> Option<UsartRead<RAW>> {
        if self.raw.raw_read_enabled() {
            None
        } else {
            Some(UsartRead::new(unsafe { core::ptr::read(&self.raw) }))
        }
    }
}

#[macro_export]
macro_rules! impl_usart_traditional {
    (
        peripheral_usart: $USART:ty,
        peripheral: $pt:ty,
        register_suffix: $n:expr,
        interrupt_r: $r:ident,
        interrupt_w: $w:ident,
        mcu: $mcu:ident,
        rx: $rxpin:ty,
        tx: $txpin:ty,
    ) => {
        $crate::paste::paste! {
            const [<FLAG_ERROR_READ_OVERFLOW $n>]: u8 = 0b01 << ($n * 2);
            const [<FLAG_FLUSH $n>]: u8 = 0b10 << ($n * 2);

            const [<READ_BUFFER_SIZE $n>]: usize = env_int::env_int!([<AVR_USART_READ_BUFFER $n>], 8);
            static mut [<READ_BUFFER $n>]: RingBuffer<[<READ_BUFFER_SIZE $n>]> = unsafe { MaybeUninit::zeroed().assume_init() };
            static mut [<READ_WAKER $n>]: Option<Waker> = None;

            const [<WRITE_BUFFER_SIZE $n>]: usize = env_int::env_int!([<AVR_USART_WRITE_BUFFER $n>], 8);
            static mut [<WRITE_BUFFER $n>]: RingBuffer<[<WRITE_BUFFER_SIZE $n>]> = unsafe { MaybeUninit::zeroed().assume_init() };
            static mut [<WRITE_WAKER $n>]: Option<Waker> = None;
            impl UsartOps2 for $USART {
                // type TX = $crate::port::Pin<$crate::port::mode::Output, $txpin>;
                // type RX = $crate::port::Pin<$crate::port::mode::Input, $rxpin>;
                fn raw_baudrate<CLOCK>(&mut self, baudrate: Baudrate<CLOCK>) {
                    self.[<ubrr $n>].write(|w| w.bits(baudrate.ubrr));
                    self.[<ucsr $n a>].write(|w| w.[<u2x $n>]().bit(baudrate.u2x));
                    // Set frame format to 8n1 for now.  At some point, this should be made
                    // configurable, similar to what is done in other HALs.
                    self.[<ucsr $n c>].write(|w| w
                        .[<umsel $n>]().usart_async()
                        .[<ucsz $n>]().chr8()
                        .[<usbs $n>]().stop1()
                        .[<upm $n>]().disabled()
                    );
                }

                fn raw_write_init(&mut self) {
                    unsafe {
                        self.[<ucsr $n b>].modify(|r, w| w.bits(r.bits())
                            .[<txen $n>]().set_bit()
                        );
                        [<WRITE_BUFFER $n>] = Default::default();
                    }
                }

                fn raw_write(&mut self, buffer: &[u8]) -> usize {
                    unsafe {
                        let wrote = [<WRITE_BUFFER $n>].write(buffer).unwrap();
                        self.[<ucsr $n b>].modify(|r, w| w.bits(r.bits()).[<udrie $n>]().set_bit());
                        wrote
                    }
                }

                fn raw_write_waker(&mut self, waker: Option<Waker>) {
                    unsafe {
                        avr_device::interrupt::free(|_| {
                            [<WRITE_WAKER $n>] = waker;
                        });
                    }
                }

                fn raw_write_flush(&mut self) {
                    unsafe {
                        USART_FLAG.and([<FLAG_FLUSH $n>], Ordering::SeqCst);
                        self.[<ucsr $n b>].modify(|r, w| w.bits(r.bits()).[<udrie $n>]().set_bit());
                    }
                }

                fn raw_write_done(&mut self) -> bool {
                    self.[<ucsr $n b>].read().[<udrie $n>]().bit_is_clear()
                }

                fn raw_write_stop(&mut self) {
                    unsafe {
                        self.[<ucsr $n b>].modify(|r, w| w.bits(r.bits()).[<udrie $n>]().clear_bit());
                        [<WRITE_WAKER $n>].take();
                    }
                }

                #[inline(always)]
                fn raw_write_enable(&mut self, enable: bool) {
                    unsafe {
                        self.[<ucsr $n b>].modify(|r, w| w.bits(r.bits()).[<txen $n>]().bit(enable))
                    }
                }

                fn raw_write_enabled(&mut self) -> bool {
                    self.[<ucsr $n b>].read().[<txen $n>]().bit()
                }


                fn raw_read_init(&mut self) {
                    unsafe {
                        self.[<ucsr $n b>].modify(|r, w| w.bits(r.bits())
                            .[<rxen $n>]().set_bit()
                        );
                        [<READ_BUFFER $n>] = Default::default();
                    }
                }

                fn raw_read(&mut self, buffer: &mut [u8]) -> usize {
                    unsafe {
                        let wrote = [<READ_BUFFER $n>].read(buffer).unwrap();
                        wrote
                    }
                }

                fn raw_read_overflow(&mut self) -> bool {
                    unsafe {
                        let v = USART_FLAG.load(Ordering::SeqCst) & [<FLAG_ERROR_READ_OVERFLOW $n>] != 0;
                        USART_FLAG.and(![<FLAG_ERROR_READ_OVERFLOW $n>], Ordering::SeqCst);
                        v
                    }
                }

                fn raw_read_waker(&mut self, waker: Option<Waker>) {
                    unsafe {
                        avr_device::interrupt::free(|_| {
                            [<READ_WAKER $n>] = waker;
                        });
                    }
                }

                fn raw_read_listen(&mut self, listen: bool) {
                    unsafe {
                        self.[<ucsr $n b>].modify(|r, w| w.bits(r.bits()).[<rxcie $n>]().bit(listen));
                    }
                }

                #[inline(always)]
                fn raw_read_enable(&mut self, enable: bool) {
                    unsafe {
                        self.[<ucsr $n b>].modify(|r, w| w.bits(r.bits()).[<rxen $n>]().bit(enable))
                    }
                }

                fn raw_read_enabled(&mut self) -> bool {
                    self.[<ucsr $n b>].read().[<rxen $n>]().bit()
                }
            }
            #[avr_device::interrupt($mcu)]
            unsafe fn $w() {
                avr_device::interrupt::free(|_| {
                    let $pt { [<USART $n>]: usart, .. } = $pt::steal();
                    match [<WRITE_BUFFER $n>].next() {
                        Some(v) => {
                            usart.[<udr $n>].write(|w| w.bits(v));
                            if USART_FLAG.load(Ordering::SeqCst) & [<FLAG_FLUSH $n>] == 0 {
                                [<WRITE_WAKER $n>].take().map(|waker| waker.wake());
                            }
                        }
                        None => {
                            if USART_FLAG.load(Ordering::SeqCst) & [<FLAG_FLUSH $n>] != 0 {
                                [<WRITE_WAKER $n>].take().map(|waker| waker.wake());
                            }
                            usart.[<ucsr $n b>].modify(|r, w| w.bits(r.bits()).[<udrie $n>]().clear_bit());
                        }
                    }
                });
            }

            #[avr_device::interrupt($mcu)]
            unsafe fn $r() {
                avr_device::interrupt::free(|_| {
                    let $pt { [<USART $n>]: usart, .. } = $pt::steal();
                    if [<READ_BUFFER $n>].write(&[usart.[<udr $n>].read().bits()]).unwrap() == 0 {
                        USART_FLAG.and([<FLAG_ERROR_READ_OVERFLOW $n>], Ordering::SeqCst);
                    }
                    [<READ_WAKER $n>].take().map(|waker| waker.wake());
                });
            }
        }
    };
}
#[cfg(feature = "usart0")] mod usart0 {

    use crate::ringbuffer::RingBuffer;
    use portable_atomic::Ordering;
    use core::mem::MaybeUninit;
    use core::task::Waker;
    use crate::UsartOps2;
    use crate::USART_FLAG;
    use embedded_io::{Read, Write};
    use avr_hal_generic::usart::Baudrate;

    macro_rules! usart_0 {
        ($i:ident) => {
            impl_usart_traditional! {
                peripheral_usart: avr_device::$i::USART0,
                peripheral: avr_device::$i::Peripherals,
                register_suffix: 0,
                interrupt_r: USART_RX,
                interrupt_w: USART_UDRE,
                mcu: $i,
                rx: atmega_hal::port::PD0,
                tx: atmega_hal::port::PD1,
            }
        };
    }

    #[cfg(feature = "atmega168")]
    usart_0!(atmega168);
    #[cfg(feature = "atmega328p")]
    usart_0!(atmega328p);
}
#[cfg(feature = "usart0")]
pub use usart0::*;
