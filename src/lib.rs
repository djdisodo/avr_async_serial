#![no_std]
#![feature(abi_avr_interrupt)]

use core::marker::PhantomData;
use core::pin::Pin;
use core::task::{Context, Poll, Waker};
use avr_hal_generic::usart::Baudrate;
use embedded_io_async::ErrorType;


use {
    atmega_hal::port,
    paste,
    avr_hal_generic::usart
};

/// Internal trait for low-level USART peripherals.
///
/// This trait defines the common interface for all USART peripheral variants.  It is used as an
/// intermediate abstraction ontop of which the [`Usart`] API is built.  **Prefer using the
/// [`Usart`] API instead of this trait.**
pub trait UsartOps2: Unpin {
    type RX;
    type TX;
    /// Enable & initialize this USART peripheral to the given baudrate.
    ///
    /// **Warning**: This is a low-level method and should not be called directly from user code.
    fn raw_init<CLOCK>(&mut self, baudrate: Baudrate<CLOCK>);

    /// Write a whole buffer to the TX buffer by sending the buffer to interrupt function
    ///
    /// do not call this while writing isn't done
    ///
    /// **Warning**: This is a low-level method and should not be called directly from user code.
    //#[cfg(feature = "async_serial")]
    fn raw_write_buffer(&mut self, buffer: &[u8], waker: Waker);

    //#[cfg(feature = "async_serial")]
    fn raw_is_write_done(&mut self) -> bool;

    //#[cfg(feature = "async_serial")]
    fn raw_is_write_stop(&mut self);
}

#[allow(dead_code)]
pub struct Usart<RAW: UsartOps2, CLOCK> {
    p: RAW,
    tx: RAW::TX,
    rx: RAW::RX,
    _clock: PhantomData<CLOCK>
}

impl<RAW: UsartOps2, CLOCK> Usart<RAW, CLOCK> {
    pub fn new(usart: RAW, tx: RAW::TX, rx: RAW::RX, rate: Baudrate<CLOCK>) -> Self {
        let mut v = Self {
            p: usart,
            tx,
            rx,
            _clock: Default::default()
        };
        v.set_baudrate(rate);
        v
    }

    pub fn set_baudrate(&mut self, rate: Baudrate<CLOCK>) {
        self.p.raw_init(rate);
    }
}

impl<RAW: UsartOps2, CLOCK> embedded_hal_async::serial::ErrorType for Usart<RAW, CLOCK> {
    type Error = Infallible;
}

impl<RAW: UsartOps2, CLOCK> embedded_hal_async::serial::Write for Usart<RAW, CLOCK> {
    #[inline(always)]
    async fn write(&mut self, words: &[u8]) -> Result<(), Self::Error> {
        Ok((AsyncWrite {
            p: unsafe { core::ptr::read(&self.p) },
            buffer: Some(words)
        }).await)
    }

    async fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(()) //no internal buffer
    }
}

impl<RAW: UsartOps2, CLOCK> ErrorType for Usart<RAW, CLOCK> { type Error = Infallible; }

impl<RAW: UsartOps2, CLOCK> embedded_io_async::Write for Usart<RAW, CLOCK> {
    #[inline(always)]
    async fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        (AsyncWrite {
            p: unsafe { core::ptr::read(&self.p) },
            buffer: Some(buf)
        }).await;
        Ok(buf.len())
    }
}

struct AsyncWrite<'a, RAW: UsartOps2> {
    p: RAW,
    buffer: Option<&'a [u8]>, // none if already sent, using option instead of bool for niche
}

impl<RAW: UsartOps2> core::future::Future for AsyncWrite<'_, RAW> {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        return if let Some(buffer) = self.as_mut().buffer.take() {
            self.p.raw_write_buffer(buffer, cx.waker().clone());
            Poll::Pending
        } else if self.p.raw_is_write_done() {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}

impl<'a, RAW: UsartOps2> Drop for AsyncWrite<'a, RAW> {
    fn drop(&mut self) {
        if self.buffer.is_none() {
            self.p.raw_is_write_stop()
        }
    }
}

use core::convert::Infallible;

#[macro_export]
macro_rules! impl_usart_traditional {
    (
        peripheral_usart: $USART:ty,
        peripheral: $pt:ty,
        register_suffix: $n:expr,
        interrupt_fn: $i:ident,
        mcu: $mcu:ident,
        rx: $rxpin:ty,
        tx: $txpin:ty,
    ) => {
        $crate::paste::paste! {
            // these static variables are guaranteed to initialized when interrupt in enabled
            // guaranteed to be dropped when interrupt is disabled
            static mut [<WRITE_BUFFER $n>]: &[u8] = &[];
            static mut [<WRITE_WAKER $n>]: Option<Waker> = None;
            impl UsartOps2 for $USART {
                type TX = $crate::port::Pin<$crate::port::mode::Output, $txpin>;
                type RX = $crate::port::Pin<$crate::port::mode::Input, $rxpin>;
                fn raw_init<CLOCK>(&mut self, baudrate: $crate::usart::Baudrate<CLOCK>) {
                    self.[<ubrr $n>].write(|w| w.bits(baudrate.ubrr));
                    self.[<ucsr $n a>].write(|w| w.[<u2x $n>]().bit(baudrate.u2x));

                    // Enable receiver and transmitter but leave interrupts disabled.
                    self.[<ucsr $n b>].write(|w| w
                        .[<txen $n>]().set_bit()
                        .[<rxen $n>]().set_bit()
                    );

                    // Set frame format to 8n1 for now.  At some point, this should be made
                    // configurable, similar to what is done in other HALs.
                    self.[<ucsr $n c>].write(|w| w
                        .[<umsel $n>]().usart_async()
                        .[<ucsz $n>]().chr8()
                        .[<usbs $n>]().stop1()
                        .[<upm $n>]().disabled()
                    );
                }

                fn raw_write_buffer(&mut self, buffer: &[u8], waker: Waker) {
                    unsafe {
                        [<WRITE_BUFFER $n>] = core::mem::transmute(buffer); // lifetime transmute
                        [<WRITE_WAKER $n>] = Some(waker);
                        self.[<ucsr $n b>].modify(|r, w| w.bits(r.bits()).[<udrie $n>]().set_bit());
                    }
                }

                fn raw_is_write_done(&mut self) -> bool {
                    self.[<ucsr $n b>].read().[<udrie $n>]().bit_is_clear()
                }

                fn raw_is_write_stop(&mut self) {
                    unsafe {
                        self.[<ucsr $n b>].modify(|r, w| w.bits(r.bits()).[<udrie $n>]().clear_bit());
                        [<WRITE_WAKER $n>].take();
                    }
                }
            }
            #[avr_device::interrupt($mcu)]
            unsafe fn $i() {
                avr_device::interrupt::free(|_| {
                    let $pt { [<USART $n>]: usart, .. } = $pt::steal();
                    if [<WRITE_BUFFER $n>].len() > 0 {
                        usart.[<udr $n>].write(|w| w.bits([<WRITE_BUFFER $n>][0]));
                        [<WRITE_BUFFER $n>] = &[<WRITE_BUFFER $n>][1..];
                    } else {
                        usart.[<ucsr $n b>].modify(|r, w| w.bits(r.bits()).[<udrie $n>]().clear_bit());
                        [<WRITE_WAKER $n>].take().map(|waker| waker.wake());
                    }
                });
            }
        }
    };
}

impl_usart_traditional! {
    peripheral_usart: avr_device::atmega328p::USART0,
    peripheral: avr_device::atmega328p::Peripherals,
    register_suffix: 0,
    interrupt_fn: USART_UDRE,
    mcu: atmega328p,
    rx: atmega_hal::port::PD0,
    tx: atmega_hal::port::PD1,
}