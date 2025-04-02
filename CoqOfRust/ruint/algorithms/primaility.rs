// Product of primes up to and including 47.
const SMALL_PRIMES: u64 = 614889782588491410;

/// Miller-Rabin primality test
///
/// See <https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test>
pub fn miller_rabin(n: u64, base: u64) -> bool {
    todo!{}
}

/// Exact 64 bit primality test
pub fn is_prime(n: u64) -> bool {
    // Sufficient set of bases for `u64`
    // See <https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test#Testing_against_small_sets_of_bases>
    // See <https://miller-rabin.appspot.com/>
    // OPT: This method <https://www.techneon.com/> ?
    // OPT: Combined basis srp
    miller_rabin(n, 2) &&
    miller_rabin(n, 325) &&
    miller_rabin(n, 9375) &&
    miller_rabin(n, 28178) &&
    miller_rabin(n, 450775) &&
    miller_rabin(n, 9780504) &&
    miller_rabin(n, 1795265022)
}
