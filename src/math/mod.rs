use std::collections::HashMap;
// use std::ops::{Deref, DerefMut};
use std::fmt;

/// Return the GCD of a, b
fn gcd(a: u64, b: u64) -> u64 {
    let (mut a, mut b) = (a, b);
    while b != 0 {
        let old_a = a;
        a = b;
        b = old_a % b;
    }
    a
}


/// Return the results of gcd-extebnded
///
/// A more detail statemetn
///
///  ```rust
/// let (d, x, r) = gcd_extended(26, 15);
/// println!("inverse = {}", x);
/// assert_eq!(3*r % 7, 1);
/// assert!(false);
///  ```
fn gcd_extended(a: i64, b: i64) -> (i64, i64, i64) {
    if b == 0 {
        return (a, 1, 0);
    }

    let (d, x, y) = gcd_extended(b, a % b);

    return (
        d,
        y,
        x-y*(a/b),
    );

}

/// Return whether a number is prime. This is O(2^n).
fn is_prime(n: u64) -> bool {
    for i in 2..n {
        if n % i == 0 {
            return false
        }
    }
    true
}

struct Factors(pub HashMap<u64, u64>);

impl fmt::Display for Factors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::from("");
        for (i, v) in self.0.iter() {
            s.push_str(i.to_string().as_str());
            s.push('^');
            s.push_str(v.to_string().as_str());
            s.push_str(" * ");
        }
        write!(f, "{}", s)
    }
}

/// Return a factors type. Probably don't even want a hashmap here.
fn factor(n: u64) -> Factors {
    let mut factors: HashMap<u64, u64> = HashMap::default();
    let mut p: u64 = n;
    let mut i: u64 = 2;

    while p != 1{
        if p % i == 0 {
            let res = if let Some(c) = factors.get(&i) {
                c+1
            } else {
                1
            };
            factors.insert(i, res);
            p /= i;
        } else {
            i += 1;
        }
    }

    Factors(factors)
}

fn fermat_prime(n: u64) -> bool {
    let u = exp(2, n-1, n);
    u == 1
}


// Return b^k ... but can't handle overflow
fn exp(b: u64, k: u64, m: u64) -> u64 {

    let mut total = 1u64;
    let mut pow = b;
    let mut k = k;

    while k > 0 {
        if k & 1 == 1 {
            total = (total*pow) % m;
        }
        pow = (pow * pow) % m;
        k /= 2;
    }

    total
}

// Return the order of a number n % p
fn order(n: u64, p: u64) -> u64 {
    let mut v = n;
    let mut order = 1;
    while v != 1 {
        v = (v * n) % p;
        order += 1;
    }
    order
}


fn sqrt(p: u64, m: u64) -> u64 {
    for root in 2..m {
        if root*root % m == p {
            return 2
        }
    }
    0
}

fn inverse(a: i64, p: i64) -> Result<i64, ()> {
    if a == 1 {
        return Ok(1)
    }

    let (_d, _x, y) = gcd_extended(p, a);

    let res = if y < 0 {
        p+y
    } else {
        y
    };

    if res == 1 {
        Err(())
    } else {
        Ok(res)
    }
}

fn slow_inverse(a: i64, p: i64) -> i64 {
    for h in 2..p {
        let e = a*h % p;
        if e == 1 {
            return h;
        }
    }
    -1
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_gcd() {
        let (_d, _x, r) = gcd_extended(26, 15);
        assert_eq!((15 * r) % 26, 1);
    }
    
    #[test]
    fn can_decompose_composite() {
        let factors = factor(3*5*7);
        let factors = factors.0;

        assert_eq!(factors.len(), 3);
        assert!(factors.contains_key(&3));
        assert!(factors.contains_key(&5));
        assert!(factors.contains_key(&7));
    }

    #[test]
    fn test_fermate_prime() {
        assert_eq!(fermat_prime(7), true);
    }
    
    #[test]
    fn test_fermat_prime() {

        println!("{}", sqrt(2, 7));
        println!("{}", sqrt(29, 35));

        for p in 3..200 {
            if !is_prime(p) {
                continue
            }

            println!(
                "{} => 2^(p-1)/2 (mod p) = 2^{} => {} ..... {}",
                p,
                (p-1)/2,
                exp(2, (p-1)/2, p),
                sqrt((p-1)/2, p),
            )
        }


        /*
        for i in 15..100000 {
             if is_prime(i) != fermat_prime(i) {
                 println!("i={} => {} != {}", i, "-", fermat_prime(i));
             }
        }
        */


        /*
        println!("{}", exp(3, 1, 2000));
        println!("{}", exp(3, 2, 2000));
        println!("{}", exp(5, 7, 2000));
        println!("{}", exp(9, 24, 1021921));
        println!("{}", exp(3, 5, 2000));
        */
        // println!("{}", exp(3, 8+4+2+1));
        // println!("{}", factor(26));
        // println!("{}", factor(3*5*29*30));
        assert!(!is_prime(27));
        assert!(gcd(15, 5) == 5);
    }


    #[test]
    fn test_inverse() -> Result<(), ()> {
        fn assert_has_inverse(n: i64, p: i64) -> Result<(), ()> {
            let g = slow_inverse(n, p);
            let h = inverse(n, p)?;
            assert_eq!(g, h);
            Ok(())
        }
        assert_has_inverse(15, 26)?;
        assert_has_inverse(4, 7)?;
        assert_has_inverse(3, 7)?;
        assert_has_inverse(3, 13)?;


        if let Ok(res) = inverse(3, 6) {
            println!("res => {}", res);
            assert!(false);
        } else {
            println!("No inverse!")
        }

        // assert_has_inverse(2, 6);
        Ok(())
    }

    #[test]
    fn test_el_gamal() {
        let p = 467;
        let g = 2;
        println!("order({}, {}) = {}", g, p, order(g, p));
        // assert!(false);
    }
}
