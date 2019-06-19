use crate::helper::RADIX;
use std::cmp::Ordering::{self, Equal, Greater, Less};

/// DigitPrimitive type used in the BigDigit type.
pub type DigitPrimitive = u8;

/// BigDigit is the type used in the BigNum field as a vector of bytes.
pub type BigDigit = Vec<DigitPrimitive>;

/// from_str is a function that will parse a decimal string
/// representation and return a BigDigit.
pub fn from_str(dec_str: &str) -> BigDigit {
    let mut num: BigDigit = dec_str
        .chars()
        .map(|x| x.to_digit(RADIX).expect("cannot pass non digits") as DigitPrimitive)
        .collect();

    // Num is stored in reverse order *little endian*, easier for arithmetic.
    num.reverse();

    num
}

/// add is the implementation function to add two BigiDigit types.
/// This is helpful because we can separate the implementation with the operator
/// implementation in big_num.
pub fn add(x: &BigDigit, y: &BigDigit) -> BigDigit {
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
    remove_leading_zeroes(result)
}

/// sub is the implementation function to subtract two BigDigit types.
/// The return is a new instance of a BigDigit.
pub fn sub(minuend: &BigDigit, addend: &BigDigit) -> BigDigit {
    let (mut result, mut carry) = (vec![], 0);

    // Retrieve the iterators for each BigDigit.
    let mut iter_1 = minuend.iter();
    let mut iter_2 = addend.iter();

    loop {
        match (iter_1.next(), iter_2.next()) {
            (None, None) => break,
            (Some(m), Some(a)) => {
                // Add 10 to enable subtraction of a lower value.
                // We will end up with overflow if m equals a -  carry.
                if m < a || m == a && carry == 1 {
                    result.push(((m + 10) - carry) - a);
                    carry = 1;
                    continue;
                }

                result.push((m - carry) - a);
                carry = 0;
            }
            (Some(m), None) => {
                let mut r = *m;

                if *m == 0 && carry > 0 {
                    r += 10;
                }

                result.push(r - carry);
                carry = r / 10;
            }
            (None, Some(a)) => {
                let mut r = *a;

                if *a == 0 && carry > 0 {
                    r += 10;
                }

                result.push(r - carry);
                carry = r / 10;
            }
        }
    }

    remove_leading_zeroes(result)
}

/// mul is the implementation function to multiply two BigDigit types.
/// The return is a new instance of a BigDigit.
pub fn mul(big: &BigDigit, small: &BigDigit) -> BigDigit {
    // Create a vector of the products to add at the end.
    let mut products: Vec<BigDigit> = vec![];

    for (i, s) in small.iter().enumerate() {
        let mut num: BigDigit = vec![];
        // Adding zeroes according to the index of i.
        for _x in 0..i {
            num.push(0);
        }

        let mut carry = 0;

        for b in big {
            let p = s * b;
            let r = (p % 10) + carry;

            carry = p / 10;

            num.push(r);
        }

        if carry > 0 {
            num.push(carry);
        }

        products.push(num)
    }

    let mut sum: BigDigit = vec![];

    for i in products {
        sum = add(&i, &sum);
    }

    sum
}

/// div is the implementation function to divide two BigDigit types.
/// The return is a new instance of a BigDigit.
pub fn div(x: BigDigit, mut y: BigDigit) -> BigDigit {
    // First pass:
    // * Assumes x is one digit.
    // * Assumes x[0] < y[0]

    // Space Complexity:
    // * result
    // * remainder

    // Time Complexity:
    // * Main loop
    // * Inner Loop
    y.reverse();
    let dividend = y;
    let divisor = x[0];

    let mut result: BigDigit = vec![];

    let mut top_carry: BigDigit = vec![];
    let mut bottom_carry: BigDigit = vec![];

    // i is the index for the dividend y.
    let mut i = 0;
    let mut j = 0;
    loop {
        if i >= dividend.len() {
            break;
        }

        // ONLY exectued on the first iteration.
        if i == 0 {
            let r = dividend[i] / divisor;
            result.push(r);

            let temp_bottom_carry = divisor * r;
            bottom_carry.push(temp_bottom_carry);

            i += 1;
            continue;
        }

        // TODO: We need to subtract the dividend[i] by the remainder.
        // I think the problem is here, we need to always shift the
        // "top carry" and
        // "bottom carry"
        if i == 1 {
            top_carry = from_str(&dividend[i - 1].to_string());
            println!("TOP CARRY: {:?}", &top_carry);
            println!("BOTTOM CARRY before sub on first iter: {:?}", &bottom_carry);
            top_carry = sub(&top_carry, &bottom_carry);
            println!("TOP CARRY: {:?}", &top_carry);
        } else {
            let big_divisor: BigDigit = vec![divisor];
            let result_digit: BigDigit = vec![result[j]];
            bottom_carry = mul(&big_divisor, &result_digit);
            println!("TOP CARRY: {:?}", &top_carry);
            println!("BOTTOM CARRY: {:?}", &bottom_carry);

            // TEMP: used for iterating the next result digit.
            j += 1;
        }

        // Bring down the next number in the dividend.
        top_carry.insert(0, dividend[i]);
        println!(
            "TOP CARRY: after brining down the next dividend {:?}",
            &top_carry
        );

        // Guess how many times the divisor goes into the dividend.
        // NEED to improve the time complexity.
        let mut guess: BigDigit = vec![0];
        let mut temp_result: BigDigit = vec![0];
        let big_divisor: BigDigit = vec![divisor];

        while compare(&temp_result, &top_carry) != Ordering::Greater {
            guess = add(&guess, &from_str("1"));
            temp_result = mul(&guess, &big_divisor);
            println!("Temp Result: {:?}", &temp_result);
            println!("Top Carry: {:?}", &top_carry);
            println!("Number of Guesses: {:?}", guess);
            println!("-----------------------------------------------");
        }

        guess = sub(&guess, &from_str("1"));
        result.insert(0, guess[0]);

        i += 1;
        println!("-----------------------------------------------");
    }

    result
}

/// compare is a function that purely comapres BigDigits.
pub fn compare(x: &BigDigit, y: &BigDigit) -> Ordering {
    // Compare the lengths.
    let (x_len, y_len) = (x.len(), y.len());

    if x_len < y_len {
        return Less;
    }

    if x_len > y_len {
        return Greater;
    }

    // Compare each primitive digit.
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
pub fn remove_leading_zeroes(mut num: BigDigit) -> BigDigit {
    // TODO: very hacky for now, enables return of 0 and adding = positive + negative.
    let mut slice_index = 0;
    num.reverse();

    for (i, x) in num.iter().enumerate() {
        // If i is already the same as the num length, meaning most likely
        // already 0, return it.
        if i == num.len() {
            return num;
        }

        // This catches whether we are removing all 0s, so we just need to return
        // the last 0.
        if slice_index + 1 == num.len() {
            break;
        }

        // Removes leading zeroes from a non-zero number.
        if *x == 0 {
            slice_index = i + 1;
        } else {
            break;
        }
    }

    // Create a slice of the vector, excluding leading zeroes.
    let slice = &num[slice_index..];

    // Create a BigDigit, reverse it and return.
    let mut result: BigDigit = slice.iter().map(|x| *x as DigitPrimitive).collect();
    result.reverse();

    result
}
