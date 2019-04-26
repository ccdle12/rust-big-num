use std::cmp::Ordering::{self, Equal, Greater, Less};

/// TEMP! Experimenting with using a DigitPrimitive type.
pub type DigitPrimitive = u8;

/// BigDigit is the type used in the BigNum field num, essentially just a vec of
/// bytes.
pub type BigDigit = Vec<DigitPrimitive>;

/// Radix is a constant used as the base for string number conversion.
pub const RADIX: u32 = 10;

/// compare_num is used to compare the BigDigit of each BigNum and return an
/// enum of Ordering. This is primarily used in the Ord trait implementation.
pub fn compare_num(x: (&BigDigit, bool), y: (&BigDigit, bool)) -> Ordering {
    // Check and compare the sign first.
    // x is negative and why is positive.
    if x.1 && !y.1 {
        return Less;
    }

    // x is positive and y is negative.
    if !x.1 && y.1 {
        return Greater;
    }

    // Switch on the Ordering according to the sign.
    let switch: bool = x.1 && y.1;

    // Compare the lengths.
    let (x_len, y_len) = (x.0.len(), y.0.len());

    if x_len < y_len {
        return sign_switch(switch, Less);
    }

    if x_len > y_len {
        return sign_switch(switch, Greater);
    }

    // Compare each primitive digit.
    for (&xi, &yi) in x.0.iter().rev().zip(y.0.iter().rev()) {
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
// the function will switch return the positive expected Ordering if b is true,
// and return the switch (opposite) Ordering if b is false.
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
