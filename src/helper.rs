use crate::big_num::{BigNum, Sign};
use std::cmp::Ordering::{self, Equal, Greater, Less};

/// Radix is a constant used as the base for string number conversion.
pub const RADIX: u32 = 10;

/// compare_num is used to compare the BigDigit of each BigNum and return an
/// enum of Ordering. This is primarily used in the Ord trait implementation.
pub(crate) fn compare_num(x: &BigNum, y: &BigNum) -> Ordering {
    // Check and compare the sign first.
    if x.sign == Sign::Negative && y.sign == Sign::Positive {
        return Less;
    }

    if x.sign == Sign::Positive && y.sign == Sign::Negative {
        return Greater;
    }

    // Switch on the Ordering according to the sign.
    let switch: bool = x.sign == Sign::Negative && y.sign == Sign::Negative;

    // Compare the lengths.
    let (x_len, y_len) = (x.num.len(), y.num.len());

    if x_len < y_len {
        return sign_switch(switch, Less);
    }

    if x_len > y_len {
        return sign_switch(switch, Greater);
    }

    // Compare each primitive digit.
    for (&xi, &yi) in x.num.iter().rev().zip(y.num.iter().rev()) {
        if xi < yi {
            return sign_switch(switch, Less);
        }

        if xi > yi {
            return sign_switch(switch, Greater);
        }
    }

    Equal
}

// internal helper function, given the sign and the positive expected Ordering,
// the function will switch and return the positive expected Ordering if b is
// true and return the opposite Ordering if b is false.
fn sign_switch(b: bool, positive_ord: Ordering) -> Ordering {
    match b {
        true => {
            return match positive_ord {
                Less => Greater,
                Greater => Less,
                _ => Equal,
            };
        }
        false => {
            return match positive_ord {
                Less => Less,
                Greater => Greater,
                _ => Equal,
            };
        }
    }
}
