use std::cmp::Ordering::{self, Equal, Greater, Less};

/// BigDigit is the type used in the BigNum field num, essentially just a vec of
/// bytes.
pub type BigDigit = Vec<u8>;

/// Radix is a constant used as the base for string number conversion.
pub const RADIX: u32 = 10;

/// compare_num is used to compare the BigDigit of each BigNum and return an
/// enum of Ordering. This is primarily used in the Ord trait implementation.
pub fn compare_num(x: &BigDigit, y: &BigDigit) -> Ordering {
    let (x_len, y_len) = (x.len(), y.len());

    if x_len < y_len {
        return Less;
    }

    if x_len > y_len {
        return Greater;
    }

    for (&xi, &yi) in x.iter().rev().zip(y.iter().rev()) {
        if xi < yi {
            return Less;
        }

        if xi > yi {
            return Greater;
        }
    }

    Equal
}

/// A helper function to remove any leading zeroes from a BigDigit.
pub fn remove_leading_zeroes(num: &mut BigDigit) {
    // This is a preferrable to using iter().rev(), since we will be unable
    // to use a mutable and immutable reference together.
    for i in (0..num.len()).rev() {
        if num[i] == 0 {
            num.remove(i);
        } else {
            break;
        }
    }
}
