#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ByteArray20 {
    array: [u8; 20],
}

impl ByteArray20 {
    pub fn to_string(&self) {

    }
}

pub fn ripemd_160() -> ByteArray20 {
    let array = [0u8; 20];
    ByteArray20 { array }
}

#[cfg(test)]
mod tests {
    // use super::*;

    // fn test_ripemd_160() {
    //     assert_eq!();
    //     9c1185a5c5e9fc54612808977ee8f548b2258d31
    // }
}
