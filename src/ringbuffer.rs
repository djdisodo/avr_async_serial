use core::cmp::min;
use core::convert::Infallible;
use core::mem::MaybeUninit;
use core::sync::atomic::Ordering;
use embedded_io::{ErrorType, Read, Write};
use portable_atomic::AtomicU8;

///custom ringbuffer implementation as we can't use usize based implementation
///*usize isn't atomic
///this code itself follows Read/Write spec but this code is used with assumption that it will return 0 when full or empty
pub struct RingBuffer<const SIZE: usize> {
    pub head: AtomicU8,
    pub tail: AtomicU8,
    data: [u8; SIZE]
}

impl<const SIZE: usize> Default for RingBuffer<SIZE> {
    fn default() -> Self {
        RingBuffer {
            head: AtomicU8::default(),
            tail: AtomicU8::default(),
            data: unsafe { MaybeUninit::uninit().assume_init() }
        }
    }
}

impl<const SIZE: usize> ErrorType for RingBuffer<SIZE> { type Error = Infallible; }

impl<const SIZE: usize> Write for RingBuffer<SIZE> {
    fn write(&mut self, mut buf: &[u8]) -> Result<usize, Self::Error> {
        let mut write = 0;
        let head = self.head.load(Ordering::SeqCst);
        let tail = (self.tail.load(Ordering::SeqCst) + (SIZE as u8) - 1) % (SIZE as u8);
        if tail == head {
            return Ok(0);
        }
        if tail < head {
            let part1 = min(SIZE - (head as usize), buf.len());
            (&mut self.data[(head as usize)..][..part1]).copy_from_slice(&buf[..part1]);
            buf = &buf[part1..];
            write += part1;
            let part2 = min(tail as usize, buf.len());
            (&mut self.data[..part2]).copy_from_slice(&buf[..part2]);
            //buf = &buf[part2..];
            write += part2;
        } else {
            let part1 = min((tail - head) as usize, buf.len());
            (&mut self.data[(head as usize)..][..part1]).copy_from_slice(&buf[..part1]);
            //buf = &buf[part1..];
            write += part1;
        }
        self.head.store(((head as usize + write) % SIZE) as u8, Ordering::SeqCst);
        Ok(write)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl<const SIZE: usize> Read for RingBuffer<SIZE> {
    fn read(&mut self, mut buf: &mut [u8]) -> Result<usize, Self::Error> {
        let head = self.head.load(Ordering::SeqCst);
        let tail = self.tail.load(Ordering::SeqCst);
        let mut read = 0;
        if tail <= head {
            let part1 = min((head - tail) as usize, buf.len());
            (&mut buf[..part1]).copy_from_slice(&self.data[(tail as usize)..][..part1]);
            //buf = &mut buf[part1..];
            read += part1;
        } else {
            let part1 = min(SIZE - (tail as usize), buf.len());
            (&mut buf[..part1]).copy_from_slice(&self.data[(tail as usize)..][..part1]);
            buf = &mut buf[part1..];
            read += part1;

            let part2 = min(head as usize, buf.len());
            (&mut buf[..part2]).copy_from_slice(&self.data[..part2]);
            //buf = &mut buf[part2..];
            read += part2;
        }
        self.tail.store(((tail as usize + read) % SIZE) as u8, Ordering::SeqCst);
        Ok(read)
    }
}

impl<const SIZE: usize> Iterator for RingBuffer<SIZE> {
    type Item = u8;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let head = self.head.load(Ordering::SeqCst);
        let tail = self.tail.load(Ordering::SeqCst);
        if head != tail {
            let item = self.data[tail as usize];
            self.tail.store((tail + 1) % SIZE as u8, Ordering::SeqCst);
            Some(item)
        } else {
            None
        }
    }
}