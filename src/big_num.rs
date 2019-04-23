use crate::helper::{compare_num, remove_leading_zeroes, BigDigit, RADIX};
use rand::Rng;
use std::cmp;
use std::cmp::Ordering::{self, Equal};
use std::fmt;
use std::ops::{Add, Sub};

/// BigNum holds a BigDigit (Vec) of bytes that represent a big number.
#[derive(Eq, Debug)]
pub struct BigNum {
    num: BigDigit,
}

// Implement Ordering for comparisons of BigNum.
impl Ord for BigNum {
    fn cmp(&self, other: &BigNum) -> Ordering {
        compare_num(&self.num, &other.num)
    }
}

impl PartialOrd for BigNum {
    fn partial_cmp(&self, other: &BigNum) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for BigNum {
    fn eq(&self, other: &BigNum) -> bool {
        match self.cmp(&other) {
            Equal => true,
            _ => false,
        }
    }
}

impl BigNum {
    /// Takes a decimal string representation, parses and returns as a BigNum.
    pub fn from_dec_str(input: &str) -> BigNum {
        let mut num: BigDigit = input
            .chars()
            .map(|x| x.to_digit(RADIX).unwrap() as u8)
            .collect();

        // Num is stored in reverse order *little endian*, easier for arithmetic.
        num.reverse();

        BigNum { num }
    }

    /// WARNING! Very basic naive random number generator below a given big
    /// number.
    pub fn gen_rand_num_below(target: &BigNum) -> BigNum {
        loop {
            let mut num = vec![0; target.num.len()];

            for i in 0..num.len() {
                num[i] = rand::thread_rng().gen_range(0, 10);
            }

            let mut below_num = BigNum { num };

            remove_leading_zeroes(&mut below_num.num);

            if below_num < *target {
                return below_num;
            }
        }
    }
}

// fmt::Display implements to_string() for BigNum.
impl fmt::Display for BigNum {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let num_str: String = self.num.iter().map(|x| x.to_string()).rev().collect();
        write!(f, "{}", num_str)
    }
}

impl Add for BigNum {
    type Output = BigNum;

    fn add(self, other: BigNum) -> BigNum {
        let mut result: BigDigit = vec![];

        let big = cmp::max(&self, &other);
        let small = cmp::min(&self, &other);

        // Iterate and calculate addition for all of i8s in small.
        let mut carry = 0;
        for i in 0..small.num.len() {
            let mut r = (big.num[i] + small.num[i]) + carry;
            carry = 0;

            if r >= 10 {
                carry = 1;
                r = r - 10;
            }

            result.push(r);
        }

        // Add the rest if there is a difference between small and big.
        for i in small.num.len()..big.num.len() {
            result.push(big.num[i] + carry);
            carry = 0;
        }

        // Catch any left over carry.
        if carry > 0 {
            result.push(carry)
        }

        // Clear any leading zeroes.
        remove_leading_zeroes(&mut result);

        BigNum { num: result }
    }
}

impl Sub for BigNum {
    type Output = BigNum;

    fn sub(self, other: BigNum) -> BigNum {
        let mut result: BigDigit = vec![];
        let mut carry = 0;

        let big = cmp::max(&self, &other);
        let small = cmp::min(&self, &other);

        for i in 0..small.num.len() {
            // Assign the each number as minuend (a), added (b) == a - b = r.
            let mut minuend = self.num[i as usize];
            let addend = other.num[i as usize];

            // The result at each column of subtraction.
            // E.g. 150 - 33:
            //  150
            // - 33
            // ----
            //  127
            let mut column_result = 0;

            if minuend < addend && carry > 0 {
                minuend += 10;
                result.push((minuend - addend) - carry);
                // carry = 1;
                continue;
            }

            // Add 10 to enable subtraction of a lower value.
            if minuend < addend {
                minuend += 10;
                carry = 1;
                result.push(minuend - addend);
                continue;
            }

            // If there is a carry, use it to calculate the column result.
            // if carry > 0 {
            //     column_result = (minuend - addend) - carry;
            //     result.push(column_result);
            //     carry = 0;
            //     continue;
            // }

            // Result at column.
            if carry > 0 {
                column_result = (minuend - addend) - carry;
            } else {
                column_result = minuend - addend;
            }

            result.push(column_result);
            carry = 0;
        }

        // Sub the rest if there is a difference between small and big.
        for i in small.num.len()..big.num.len() {
            result.push(big.num[i] - carry);
            carry = 0;
        }

        remove_leading_zeroes(&mut result);

        BigNum { num: result }
    }
}

#[cfg(test)]
mod addition_tests {
    use super::*;

    #[test]
    fn simple_add_1() {
        let x = BigNum::from_dec_str("149");
        let y = BigNum::from_dec_str("1");
        let result = x + y;

        assert_eq!(result.to_string(), "150");
    }

    #[test]
    fn simple_add_2() {
        let x = BigNum::from_dec_str("149");
        let y = BigNum::from_dec_str("320");
        let result = x + y;

        assert_eq!(result.to_string(), "469");
    }

    #[test]
    fn simple_add_3() {
        let x = BigNum::from_dec_str("4362911");
        let y = BigNum::from_dec_str("9732360");
        let result = x + y;

        assert_eq!(result.to_string(), "14095271");
    }

    #[test]
    fn big_numbers_add_1() {
        let x = BigNum::from_dec_str("1437693012945712340532450954326891");
        let y = BigNum::from_dec_str("23948324543257904183523168231945698423765234");
        let result = x + y;

        assert_eq!(
            result.to_string(),
            "23948324544695597196468880572478149378092125"
        )
    }

    #[test]
    fn big_numbers_add_2() {
        let x = BigNum::from_dec_str("132593257943285632497568497562319847013298473190285691205710294310234981024823104984326234523142354326");
        let y = BigNum::from_dec_str("4835743185712987423498564329587312094803981759438257493257943085012394831902473295632975643829765987439210847319028471398471234");
        let result = x + y;

        assert_eq!(
            result.to_string(),
            "4835743185712987423498564462180570038089614257006755055577790098310868022188164501343269954064747012262315831645262994540825560"
        )
    }

    #[test]
    fn leading_zeros_1() {
        let x = BigNum::from_dec_str("0000000000000000000023");
        let y = BigNum::from_dec_str("02");
        let result = x + y;

        assert_eq!(result.to_string(), "25");
    }

    #[test]
    fn leading_zeros_2() {
        let x = BigNum::from_dec_str("0000000000000000000000000000000023");
        let y = BigNum::from_dec_str("3219857349857439285798234981234809231850192485043985034295804329579083415710932857109485430925709128430219473210985732190857213908473092874039218470139284710923472310948");
        let result = x + y;

        assert_eq!(
            result.to_string(),
            "3219857349857439285798234981234809231850192485043985034295804329579083415710932857109485430925709128430219473210985732190857213908473092874039218470139284710923472310971"
        );
    }

}

#[cfg(test)]
mod subtraction_tests {
    use super::*;

    #[test]
    fn subtraction_1() {
        let x = BigNum::from_dec_str("10");
        let y = BigNum::from_dec_str("2");

        let result = x - y;
        assert_eq!(result, BigNum::from_dec_str("8"));
    }

    #[test]
    fn subtraction_2() {
        let x = BigNum::from_dec_str("150");
        let y = BigNum::from_dec_str("33");

        let result = x - y;
        assert_eq!(result, BigNum::from_dec_str("117"));
    }

    #[test]
    fn subtraction_3() {
        let x = BigNum::from_dec_str("7");
        let y = BigNum::from_dec_str("5");

        let result = x - y;
        assert_eq!(result, BigNum::from_dec_str("2"));
    }

    #[test]
    fn subtraction_4() {
        let x = BigNum::from_dec_str("120");
        let y = BigNum::from_dec_str("33");

        let result = x - y;
        assert_eq!(result, BigNum::from_dec_str("87"));
    }

    // #[test]
    // fn subtraction_5() {
    // let x = BigNum::from_dec_str("1238758592436584327503819247913286418235761302847321985648723569230814712309857312958613290846321904872310984732195847389256438275623014781239084731290847");
    // let y = BigNum::from_dec_str("32481237549385701982745329084730921847193824712385618297563298174321894128356321987409312749031286583721640912387439201865091265019254");

    // let result = x - y;

    // assert_eq!(result, BigNum::from_dec_str("1238758592436584327471338010363900716253015973762591063801529744518429094012294014784291396717965582884901671983164560805534797363235575579373993466271593"));
    // }
}

#[cfg(test)]
mod comparison_tests {
    use super::*;

    #[test]
    fn compare_1() {
        let x = BigNum::from_dec_str("132593257943285632497568497562319847013298473190285691205710294310234981024823104984326234523142354326");
        let y = BigNum::from_dec_str("4835743185712987423498564329587312094803981759438257493257943085012394831902473295632975643829765987439210847319028471398471234");

        assert!(x < y);
        assert!(y > x);
        assert!(x != y);
    }

    #[test]
    fn compare_2() {
        let x = BigNum::from_dec_str("45");
        let y = BigNum::from_dec_str("52");

        assert!(x < y);
        assert!(y > x);
        assert!(y != x);
    }

    #[test]
    fn compare_3() {
        let x = BigNum::from_dec_str("132598123512354");
        let y = BigNum::from_dec_str("132598123512354");

        assert_eq!(x, y);
        assert!(x == y);
    }

    #[test]
    fn compare_4() {
        let x = BigNum::from_dec_str("132593257943285632497568497562319847013298473190285691205710294310234981024823104984326234523142354326");
        let y = BigNum::from_dec_str("4835743185712987423498564329587312094803981759438257493257943085012394831902473295632975643829765987439210847319028471398471234");

        assert_eq!(cmp::max(&x, &y), &y);
        assert_eq!(cmp::min(&x, &y), &x);
    }

    #[test]
    fn compare_5() {
        let x = BigNum::from_dec_str("42");
        let y = BigNum::from_dec_str("229");

        assert!(x < y);
    }
}

#[cfg(test)]
mod random_number_tests {
    use super::*;

    #[test]
    fn generate_random_number_1() {
        let x = BigNum::from_dec_str("42");
        let y = BigNum::gen_rand_num_below(&x);

        println!("x: {}", x);
        println!("y: {}", y);

        assert!(y < x);
    }

    #[test]
    fn generate_random_number_2() {
        let x = BigNum::from_dec_str("132593257943285632497568497562319847013298473190285691205710294310234981024823104984326234523142354326");
        let y = BigNum::gen_rand_num_below(&x);

        assert!(y < x);
    }
}
