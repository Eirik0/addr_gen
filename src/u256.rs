use std::error::Error;
use std::fmt;
use std::ops::{AddAssign, SubAssign};

const MAX_U128_LEFT: u128 = 0xFFFFFFFFFFFFFFFF0000000000000000;
const MAX_U128_RIGHT: u128 = 0x0000000000000000FFFFFFFFFFFFFFFF;
const FIRST_BIT_FLAG: u128 = 0x80000000000000000000000000000000;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct U256 {
    pub d0: u128,
    pub d1: u128,
}

impl U256 {
    pub const MAX_U128: u128 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

    pub fn new(d0: u128, d1: u128) -> Self {
        U256 { d0, d1 }
    }

    pub fn from_u128(d1: u128) -> Self {
        U256 { d0: 0, d1 }
    }

    fn parse_digit(digit: &u8) -> Result<u128, U256ParseError> {
        match digit {
            nibble @ b'A'...b'F' => Ok((nibble + 10 - b'A') as u128),
            nibble @ b'a'...b'f' => Ok((nibble + 10 - b'a') as u128),
            nibble @ b'0'...b'9' => Ok((nibble - b'0') as u128),
            _ => Err(U256ParseError::UnexpectedCharacter),
        }
    }

    fn hex_to_u128(hex_digits: &[u8]) -> Result<u128, U256ParseError> {
        let mut d = 0;
        for i in 0..hex_digits.len() {
            d <<= 4;
            d |= U256::parse_digit(&hex_digits[i])?;
        }
        Ok(d)
    }

    pub fn from_hex_str(s: &str) -> Result<U256, U256ParseError> {
        let hex_digits = s.as_bytes();
        let len = hex_digits.len();
        if len == 0 {
            return Err(U256ParseError::Empty);
        } else if len > 64 {
            return Err(U256ParseError::Overflow);
        }
        if len >= 32 {
            let start = &hex_digits[..len - 32];
            let end = &hex_digits[len - 32..];
            Ok(U256 {
                d0: U256::hex_to_u128(start)?,
                d1: U256::hex_to_u128(end)?,
            })
        } else {
            Ok(U256 {
                d0: 0,
                d1: U256::hex_to_u128(hex_digits)?,
            })
        }
    }

    fn u128_to_hex(digit: u128) -> Vec<u8> {
        let mut d = digit;
        let mut bytes = vec![0u8; 32];
        for i in (0..32).rev() {
            bytes[i as usize] = match d & 0xF {
                nibble @ 0...9 => b'0' + nibble as u8,
                nibble => b'a' + nibble as u8 - 10,
            };
            d >>= 4;
        }
        bytes
    }

    pub fn to_hex_string(&self) -> String {
        let mut bytes = U256::u128_to_hex(self.d0);
        bytes.append(&mut U256::u128_to_hex(self.d1));
        let mut last_non_zero = 0;
        for i in 0..64 {
            if bytes[i] != b'0' {
                last_non_zero = i;
                break;
            }
        }
        String::from_utf8((&bytes[last_non_zero..]).to_vec()).unwrap()
    }

    pub fn to_base58_string(&self) {}

    pub fn mul_u128(lhs: &u128, rhs: &u128) -> U256 {
        // k = 2^64
        // lhs = k * l_d0 + l_d1
        // rhs = k * r_d0 + r_d1
        // lhs * rhs = k^2 * (l_d0 * r_d0) + k * (l_d0 * r_d1 + l_d1 * r_d0) + (l_d1 * r_d1)
        let l_d0 = (lhs & MAX_U128_LEFT) >> 64;
        let l_d1 = lhs & MAX_U128_RIGHT;
        let r_d0 = (rhs & MAX_U128_LEFT) >> 64;
        let r_d1 = rhs & MAX_U128_RIGHT;

        let mut d0 = l_d0 * r_d0;
        let s2 = l_d0 * r_d1;
        let s3 = l_d1 * r_d0;
        let d1 = l_d1 * r_d1;

        let s23_l = ((s2 & MAX_U128_LEFT) >> 64) + ((s3 & MAX_U128_LEFT) >> 64);
        let s23_r = (s2 & MAX_U128_RIGHT) + (s3 & MAX_U128_RIGHT);

        let (d1, carry_d1) = d1.overflowing_add(s23_r << 64);

        d0 += s23_l;
        if carry_d1 {
            d0 += 1;
        }

        U256 { d0, d1 }
    }

    pub fn overflowing_add_assign(&mut self, rhs: &U256) -> bool {
        let (d1, carry_d1) = self.d1.overflowing_add(rhs.d1);
        self.d1 = d1;

        let (d0, carry_d0) = self.d0.overflowing_add(rhs.d0);

        if carry_d1 {
            let (d0, carry_carry) = d0.overflowing_add(1);
            self.d0 = d0;
            carry_d0 || carry_carry
        } else {
            self.d0 = d0;
            carry_d0
        }
    }

    pub fn add_assign(&mut self, rhs: u128) {
        let (d1, carry) = self.d1.overflowing_add(rhs);
        self.d1 = d1;
        if carry {
            self.d0 += 1;
        }
    }

    pub fn overflowing_add_assign_d0(&mut self, rhs: u128) -> bool {
        let (d0, carry) = self.d0.overflowing_add(rhs);
        self.d0 = d0;
        carry
    }

    pub fn sub(&self, rhs: &U256) -> U256 {
        // Assumes d0 >= rhs.d0
        let d0 = self.d0 - rhs.d0;
        if rhs.d1 > self.d1 {
            U256 {
                d0: d0 - 1,
                d1: self.d1 + U256::MAX_U128 - rhs.d1 + 1,
            }
        } else {
            U256 {
                d0,
                d1: self.d1 - rhs.d1,
            }
        }
    }

    pub fn overflowing_double(&mut self) -> bool {
        let carry_d0 = self.d0 & FIRST_BIT_FLAG == FIRST_BIT_FLAG;
        let carry_d1 = self.d1 & FIRST_BIT_FLAG == FIRST_BIT_FLAG;
        self.d1 <<= 1;
        self.d0 <<= 1;
        if carry_d1 {
            self.d0 |= 1;
        }
        carry_d0
    }
}

impl<'a> SubAssign<&'a U256> for U256 {
    fn sub_assign(&mut self, rhs: &'a U256) {
        // Assumes d0 >= rhs.d0
        self.d0 -= rhs.d0;
        if rhs.d1 > self.d1 {
            self.d1 += U256::MAX_U128 - rhs.d1 + 1;
            self.d0 -= 1;
        } else {
            self.d1 -= rhs.d1;
        }
    }
}

impl AddAssign<u128> for U256 {
    fn add_assign(&mut self, rhs: u128) {
        // Assumes self + rhs < 2^256
        let (d1, carry_d1) = self.d1.overflowing_add(rhs);
        self.d1 = d1;

        if carry_d1 {
            self.d0 += 1;
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum U256ParseError {
    Empty,
    UnexpectedCharacter,
    Overflow,
}

impl Error for U256ParseError {
    fn description(&self) -> &str {
        match self {
            U256ParseError::Empty => "Empty string",
            U256ParseError::UnexpectedCharacter => "Unexpected character",
            U256ParseError::Overflow => "Overflow",
        }
    }
}

impl fmt::Display for U256ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Error while parsing U256")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAX_U128: u128 = 340_282_366_920_938_463_463_374_607_431_768_211_455u128;

    #[test]
    fn test_hex_to_u256() {
        assert_eq!(U256 { d0: 0, d1: 1 }, U256::from_hex_str("1").unwrap());
        assert_eq!(U256 { d0: 0, d1: 15 }, U256::from_hex_str("f").unwrap());
        assert_eq!(U256 { d0: 0, d1: 15 }, U256::from_hex_str("F").unwrap());
        assert_eq!(U256 { d0: 0, d1: 31 }, U256::from_hex_str("1f").unwrap());
        assert_eq!(
            U256 {
                d0: 0,
                d1: MAX_U128
            },
            U256::from_hex_str("ffffffffffffffffffffffffffffffff").unwrap()
        );
        assert_eq!(
            U256 { d0: 1, d1: 0 },
            U256::from_hex_str("100000000000000000000000000000000").unwrap()
        );
    }

    #[test]
    fn test_hex_to_u256_error() {
        assert_eq!(Err(U256ParseError::Empty), U256::from_hex_str(""));
        assert_eq!(
            Err(U256ParseError::UnexpectedCharacter),
            U256::from_hex_str("g")
        );
        assert_eq!(
            Err(U256ParseError::Overflow),
            U256::from_hex_str("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
        );
    }

    #[test]
    fn test_to_hex_string() {
        let hex_str = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
        assert_eq!(
            hex_str,
            U256::from_hex_str(hex_str).unwrap().to_hex_string()
        );
        assert_eq!("f", U256::from_hex_str("f").unwrap().to_hex_string());
    }

    #[test]
    fn test_mul_u128() {
        let product = U256::new(
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE,
            0x00000000000000000000000000000001,
        );
        let multiplication = U256::mul_u128(&MAX_U128, &MAX_U128);
        assert_eq!(product, multiplication);
    }

    #[test]
    fn test_compare() {
        assert!(U256::new(0, 1) > U256::new(0, 0));
        assert!(U256::new(0, 1) >= U256::new(0, 1));
        assert!(U256::new(1, 0) > U256::new(0, 1));
        assert!(U256::new(1, 1) > U256::new(1, 0));
        assert!(U256::new(1, 1) >= U256::new(1, 1));
        assert!(!(U256::new(0, 1) <= U256::new(0, 0)));
        assert!(!(U256::new(0, 1) < U256::new(0, 1)));
        assert!(!(U256::new(1, 0) <= U256::new(0, 1)));
        assert!(!(U256::new(1, 1) <= U256::new(1, 0)));
        assert!(!(U256::new(1, 1) < U256::new(1, 1)));
    }

    #[test]
    fn test_overflowing_add_assign() {
        let mut big_n = U256::new(MAX_U128, MAX_U128 - 1);
        let one = U256::from_u128(1);
        let overflow = big_n.overflowing_add_assign(&one);
        assert!(!overflow);
        assert_eq!(U256::new(MAX_U128, MAX_U128), big_n);
        let overflow = big_n.overflowing_add_assign(&one);
        assert!(overflow);
        assert_eq!(U256::from_u128(0), big_n);
        let mut n1 = U256::from_hex_str("2000007a4fffffffffffffffefffff859fff1601b").unwrap();
        let n2 = U256::from_hex_str(
            "fffffffffffffffffffffffdfffff85b0000000000000001000007a5000e9c16",
        ).unwrap();
        let n1_plus_n2 = U256::from_hex_str(
            "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc31",
        ).unwrap();
        let overflow = n1.overflowing_add_assign(&n2);
        assert!(!overflow);
        assert_eq!(n1_plus_n2, n1);
    }

    #[test]
    fn test_sub_assign() {
        let mut n = U256::new(1, 1);
        let one = U256::from_u128(1);
        n -= &one;
        assert_eq!(U256::new(1, 0), n);
        n -= &one;
        assert_eq!(U256::new(0, MAX_U128), n);
        let mut two = U256::from_hex_str(
            "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc31",
        ).unwrap();
        let p = U256 {
            d0: 0xFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF,
            d1: 0xFFFFFFFF_FFFFFFFF_FFFFFFFE_FFFFFC2F,
        };
        two -= &p;
        assert_eq!(U256::from_u128(2), two);
    }

    #[test]
    fn test_add_assign() {
        let mut n = U256::new(0, MAX_U128);
        n += 1;
        assert_eq!(U256::new(1, 0), n);
        n += 1;
        assert_eq!(U256::new(1, 1), n);
    }
}
