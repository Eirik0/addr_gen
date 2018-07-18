use std::ops::{AddAssign, MulAssign, Mul};

use u256::U256;

// P = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
const P_D1: u128 = 0xFFFFFFFF_FFFFFFFF_FFFFFFFE_FFFFFC2F;
const P_MINUS_2_D1: u128 = 0xFFFFFFFF_FFFFFFFF_FFFFFFFE_FFFFFC2D;
const P: U256 = U256 {d0: 0xFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF, d1: P_D1};

// const G_X: U256 = U256 {d0: 0x79BE667EF9DCBBAC55A06295CE870B07, d1:0x029BFCDB2DCE28D959F2815B16F81798};
// const G_Y: U256 = U256 {d0: 0x483ADA7726A3C4655DA4FBFC0E1108A8, d1: 0xFD17B448A68554199C47D08FFB10D4B8};
// const G: S256Point = S256Point::Point(Point {x: FieldElement {n: G_X}, y: FieldElement {n: G_Y}});

// const N: U256 = U256 {d0: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE, d1: 0xBAAEDCE6AF48A03BBFD25E8CD0364141};

const TWO_POW_256_MOD_P: u128 = 0x1_000003D1;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FieldElement {
    n: U256,
}

impl FieldElement {
    pub fn new(n: U256) -> Self {
        let mut ele = FieldElement {n};
        FieldElement::normalize_mod_p(&mut ele.n);
        ele 
    }

    fn normalize_mod_p(n: &mut U256) {
        if n.d0 == U256::MAX_U128 && n.d1 >= P_D1 {
            n.d0 = 0;
            n.d1 -= &P_D1;
        }
    }

    pub fn add_assign(&mut self, rhs: &FieldElement) {
        if self.n.overflowing_add_assign(&rhs.n) {
            self.n.add_assign(TWO_POW_256_MOD_P)
        }
        FieldElement::normalize_mod_p(&mut self.n);
    }

    pub fn sub_assign(&mut self, rhs: &FieldElement) {
        let rhs_neg = P.sub(&rhs.n);
        if self.n.overflowing_add_assign(&rhs_neg) {
            self.n.add_assign(TWO_POW_256_MOD_P)
        }
        FieldElement::normalize_mod_p(&mut self.n);
    }

    pub fn mul_assign(&mut self, rhs: &FieldElement) {
        let d0 = self.n.d0;
        let d1 = self.n.d1;

        self.n = U256::mul_u128(&d0, &rhs.n.d0);
        self.mul_assign_2_pow_256();

        let mut l0r1 = FieldElement::new(U256::mul_u128(&d0, &rhs.n.d1));
        l0r1.mul_assign_2_pow_128();
        let mut l1r0 = FieldElement::new(U256::mul_u128(&d1, &rhs.n.d0));
        l1r0.mul_assign_2_pow_128();

        self.add_assign(&l0r1);
        self.add_assign(&l1r0);
        self.add_assign(&FieldElement::new(U256::mul_u128(&d1, &rhs.n.d1)));
    }

    pub fn div_assign(&mut self, rhs: &FieldElement) {
        self.mul_assign(&rhs.invert());
    }

    pub fn mul_assign_2_pow_128(&mut self) {
        // let k = 2^128
        // let q = k^2 = 2^256 (mod p)
        // let n = d0 * k + d1
        // => n * k (mod p) = ((d0 * q) (mod p) + (d1 * k) (mod p)) (mod p)
        let d0 = self.n.d0;
        let d1 = self.n.d1;

        self.n = U256::mul_u128(&d0, &TWO_POW_256_MOD_P);
        if self.n.overflowing_add_assign_d0(d1) {
            self.n.add_assign(TWO_POW_256_MOD_P);
        }

        FieldElement::normalize_mod_p(&mut self.n);
    }

    pub fn mul_assign_2_pow_256(&mut self) {
        // let k = 2^128
        // let q = k^2 = 2^256 (mod p)
        // let n = d0 * k + d1
        // => (n * k^2) (mod p) = (d0 * k + d1) * q (mod p)
        // = ((d0 * k * q) (mod p) + (d1 * q) (mod p)) (mod p)
        let d0 = self.n.d0;
        let d1 = self.n.d1;

        self.n = U256::mul_u128(&d0, &TWO_POW_256_MOD_P);
        self.mul_assign_2_pow_128();
        self.add_assign(&FieldElement::new(U256::mul_u128(&d1, &TWO_POW_256_MOD_P)));
    }

    pub fn negate_assign(&mut self) {
        self.n = P.sub(&self.n);
    }

    pub fn double_assign(&mut self) {
        if self.n.overflowing_double() {
            self.n.add_assign(TWO_POW_256_MOD_P);
        }
        FieldElement::normalize_mod_p(&mut self.n);
    }

    pub fn triple_assign(&mut self) {
        let n = self.n.clone();
        self.double_assign();
        if self.n.overflowing_add_assign(&n) {
            self.n.add_assign(TWO_POW_256_MOD_P);
        }
        FieldElement::normalize_mod_p(&mut self.n);
    }

    pub fn square_assign(&mut self) {
        let d0 = self.n.d0;
        let d1 = self.n.d1;

        self.n = U256::mul_u128(&d0, &d0);
        self.mul_assign_2_pow_256();
        
        let mut l0l1 = FieldElement::new(U256::mul_u128(&d0, &d1));
        l0l1.mul_assign_2_pow_128();

        self.add_assign(&l0l1);
        self.add_assign(&l0l1);
        self.add_assign(&FieldElement::new(U256::mul_u128(&d1, &d1)));
    }

    pub fn invert(&self) -> FieldElement {
        let mut inv = self.clone();
        let mut square = self.clone();
        let mut flag = 2u128;
        while flag != 0x100000000 {
            square.square_assign();
            if P_MINUS_2_D1 & flag == flag {
                inv.mul_assign(&square);
            }
            flag <<= 1;
        }
        square.square_assign();
        let mut i = 33;
        // After the 33st least significant bit, P - 2 is all 1s
        while i < 256 {
            square.square_assign();
            inv.mul_assign(&square);
            i += 1;
        }
        inv
    }
}

impl<'a> Mul<&'a FieldElement> for FieldElement {
    type Output = FieldElement;

    fn mul(self, rhs: &'a FieldElement) -> FieldElement {
        // let k = 2^128
        // l0 = self.n.d0; l1 = self.n.d1; r0 = rhs.n.d0; r1 = rhs.n.d1;
        // self * rhs mpd p = (k * l0 + l1)(k * r0 + r1) mod p
        // = (k^2 * l0 * r0 + k * l0 * r1 + k * l1 * r0 + l1 * r1) mod p
        // = ((k^2 * l0 * r0) (mod p) + (k * l0 * r1) (mod p) + (k * l1 * r0) (mod p) + (l1 * r1) mod p) mod p
        let mut l0r0 = FieldElement::new(U256::mul_u128(&self.n.d0, &rhs.n.d0));
        l0r0.mul_assign_2_pow_256(); // prod1 = l0r0 * k^2
        let mut l0r1 = FieldElement::new(U256::mul_u128(&self.n.d0, &rhs.n.d1));
        l0r1.mul_assign_2_pow_128(); // prod2 = l0r1 * k
        let mut l1r0 = FieldElement::new(U256::mul_u128(&self.n.d1, &rhs.n.d0));
        l1r0.mul_assign_2_pow_128(); // prod3 = l1r0 * k
        let l1r1 = FieldElement::new(U256::mul_u128(&self.n.d1, &rhs.n.d1)); // prod4 = l1r1 * 1

        l0r0.add_assign(&l0r1);
        l0r0.add_assign(&l1r0);
        l0r0.add_assign(&l1r1);

        l0r0
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum S256Point {
    Point(Point),
    Infinity,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Point {
    pub x: FieldElement,
    pub y: FieldElement,
}

impl Point {
    pub fn new(x: FieldElement, y: FieldElement) -> Self {
        Point {x, y}
    }

    pub fn double(&mut self) {
        // let s = (3 * self.x * self.x) / (2 * self.y);
        // let x = s * s - 2 * self.x;
        // let y = s * (self.x - x) - self.y;
        let mut s = self.x.clone();
        s.square_assign();
        s.triple_assign();
        let mut y_mul_2 = self.y.clone();
        y_mul_2.double_assign();
        s.div_assign(&y_mul_2);

        let mut x = self.x.clone();

        self.x.double_assign();
        self.x.negate_assign();
        let mut s_sq = s.clone();
        s_sq.square_assign();
        self.x.add_assign(&s_sq);

        self.y.negate_assign();
        x.sub_assign(&self.x);
        x.mul_assign(&s);
        self.y.add_assign(&x);
    }
}

impl<'a> MulAssign<&'a U256> for S256Point {
    fn mul_assign(&mut self, rhs: &'a U256) {
        match self {
            S256Point::Point(point) => {
                let mut double = point.clone();
                let mut flag = 1u128;
                while flag != 0 {
                    if rhs.d1 & flag == flag {
                        *self += &double;
                    }
                    double.double();
                    flag <<= 1;
                }
                flag = 1u128;
                while flag != 0 {
                    if rhs.d0 & flag == flag {
                        *self += &double;
                    }
                    double.double();
                    flag <<= 1;
                }
            },
            S256Point::Infinity => {},
        }
    }
}

impl<'a> AddAssign<&'a Point> for S256Point {
    fn add_assign(&mut self, rhs: &'a Point) {
        match self {
            S256Point::Point(lhs) => {
                if lhs.x == rhs.x {
                    if rhs.y == lhs.y {
                        lhs.double();
                    } else {
                        *self = S256Point::Infinity;
                    }
                } else {
                    // let s = (rhs.y - lhs.y) / (rhs.x - lhs.x);
                    // let x = s * s - lhs.x - rhs.x;
                    // let y = s * (lhs.x - x) - lhs.y;
                    // S256Point::Point(Point {x, y})
                }
            },
            S256Point::Infinity => *self = S256Point::Point(rhs.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::u256::*;

    const P_MINUS_1: U256 = U256 {d0: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, d1: 0xFFFFFFFF_FFFFFFFF_FFFFFFFE_FFFFFC2E};
    const P_MINUS_2: U256 = U256 {d0: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, d1: 0xFFFFFFFF_FFFFFFFF_FFFFFFFE_FFFFFC2D};

    #[test]
    pub fn test_new_field_element() {
        let p_plus_2 = U256::from_hex_str("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc31").unwrap();
        assert_eq!(FieldElement::new(U256::from_u128(2)), FieldElement::new(p_plus_2));
    }

    #[test]
    fn test_field_element_add_assign() {
        // ((p - 1) += 1) += 1)
        let mut n = FieldElement::new(P_MINUS_1);
        let one = FieldElement::new(U256::from_u128(1));
        n.add_assign(&one);
        assert_eq!(FieldElement::new(P), n);
        n.add_assign(&one);
        assert_eq!(one, n);
        // (p - 1) += (p - 1)
        let mut n1 = FieldElement::new(P_MINUS_1);
        let n2 = FieldElement::new(P_MINUS_1);
        n1.add_assign(&n2);
        assert_eq!(FieldElement::new(P_MINUS_2), n1);
        // (...) += (...)
        let mut n1 = FieldElement::new(U256::from_hex_str("2000007a4fffffffffffffffefffff859fff1601b").unwrap());
        let n2 = FieldElement::new(U256::from_hex_str("fffffffffffffffffffffffdfffff85b0000000000000001000007a5000e9c16").unwrap());
        n1.add_assign(&n2);
        assert_eq!(FieldElement::new(U256::from_u128(2)), n1);
    }

    #[test]
    fn test_field_element_mul_assign_2_pow_128() {
        let two_pow_256 = FieldElement::new(U256::from_u128(TWO_POW_256_MOD_P));
        let mut n = FieldElement::new(U256::new(1, 0));
        n.mul_assign_2_pow_128();
        assert_eq!(two_pow_256, n);
    }

    #[test]
    fn test_field_element_mul_assign_2_pow_256() {
        let two_pow_256 = FieldElement::new(U256::from_u128(TWO_POW_256_MOD_P));
        let mut n = FieldElement::new(U256::new(0, 1));
        n.mul_assign_2_pow_256();
        assert_eq!(two_pow_256, n);
    }

    #[test]
    fn test_field_element_mul() {
        let two = FieldElement::new(U256::from_u128(2));
        let four = FieldElement::new(U256::from_u128(4));
        let eight = FieldElement::new(U256::from_u128(8));
        assert_eq!(eight, four * &two);
        let n1 = FieldElement::new(P_MINUS_1);
        let n2 = FieldElement::new(P_MINUS_2);
        assert_eq!(two, n1 * &n2);
    }

    #[test]
    fn test_invert() {
        let one = FieldElement::new(U256::from_u128(1));
        let p_minus_one = FieldElement::new(P_MINUS_1);
        assert_eq!(one, one.invert());
        assert_eq!(p_minus_one, p_minus_one.invert());
    }
}
