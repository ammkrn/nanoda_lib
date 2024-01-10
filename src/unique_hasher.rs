//! Hasher for unique values
pub struct UniqueHasherBuilder;

pub struct UniqueHasher {
    digest: u64,
}

impl Default for UniqueHasher {
    fn default() -> UniqueHasher { UniqueHasher::new() }
}

impl UniqueHasher {
    pub const fn new() -> Self { Self { digest: 0 } }

    #[inline]
    pub fn set_digest(&mut self, val: u64) {
        //One time only
        debug_assert_eq!(self.digest, 0);
        self.digest = val;
    }
}

impl core::hash::BuildHasher for UniqueHasherBuilder {
    type Hasher = UniqueHasher;

    #[inline]
    fn build_hasher(&self) -> Self::Hasher { UniqueHasher::new() }
}

impl core::hash::Hasher for UniqueHasher {
    #[inline]
    fn finish(&self) -> u64 { self.digest }

    #[inline]
    fn write(&mut self, _: &[u8]) {
        panic!("should not be used");
    }

    #[inline]
    fn write_u64(&mut self, i: u64) { self.set_digest(i); }
}
