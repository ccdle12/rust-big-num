use crate::big_num::{BigNum, Sign};
use std::cmp::Ordering::{self, Equal, Greater, Less};

/// DigitPrimitive type used in the BigDigit type.
pub type DigitPrimitive = u8;

/// BigDigit is the type used in the BigNum field num, essentially just a vec of
/// bytes.
pub type BigDigit = Vec<DigitPrimitive>;

/// Radix is a constant used as the base for string number conversion.
pub const RADIX: u32 = 10;

// TODO: (ccdle12) Separate Big Digit and its functions to own file.
/// add_big_digits is the implementation function to add two BigiDigit types.
/// This is helpful because we can separate the implementation with the operator
/// implementation in big_num.
pub(crate) fn add_big_digits(x: &BigDigit, y: &BigDigit) -> BigDigit {
    // Initialise the result vec and carry.
    let (mut result, mut carry) = (vec![], 0);

    // Retrieve the iterators for each BigDigit.
    let mut iter_1 = x.iter();
    let mut iter_2 = y.iter();

    // Add both numbers at each column, this is achieved by iterating over
    // different sized BigDigits by calling `next()` on each iterator and
    // checking the Option<> Enum value for Some or None. We can continue
    // iterating over one list when the other is exhausted. We also add
    // and update carry, we can mod the result by 10 to give us the
    // remainder if the total is above 10 and we can reset the carry by
    // dividing by 10. Since Rust will floor the division, if there is a
    // carry it will always be 1 and if its below 10 carry will always be 0.
    loop {
        match (iter_1.next(), iter_2.next()) {
            (None, None) => break,
            (Some(x), Some(y)) => {
                carry += x;
                carry += y;
            }
            (Some(x), None) => {
                carry += x;
            }
            (None, Some(y)) => {
                carry += y;
            }
        }

        result.push(carry % 10);
        carry = carry / 10;
    }

    // Catch any lingering carry.
    if carry == 1 {
        result.push(1);
    }

    // Clear any leading zeroes.
    remove_leading_zeroes(&mut result);

    result
}

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
