use crate::helper::{compare_num, remove_leading_zeroes, BigDigit, DigitPrimitive, RADIX};
use rand::Rng;
use std::cmp;
use std::cmp::Ordering::{self, Equal};
use std::fmt;
use std::ops::{Add, Sub};

/// BigNum holds a BigDigit (Vec) of bytes that represent a big number.
#[derive(Eq, Debug)]
pub struct BigNum {
    num: BigDigit,
    sign: bool,
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
        let mut num: BigDigit;
        let mut sign: bool = false;

        // TODO: can this be made without duplication?
        if input.starts_with('-') {
            sign = true;
            num = input
                .chars()
                .skip(1)
                .map(|x| x.to_digit(RADIX).unwrap() as DigitPrimitive)
                .collect();
        } else {
            num = input
                .chars()
                .map(|x| x.to_digit(RADIX).unwrap() as DigitPrimitive)
                .collect();
        }

        // Num is stored in reverse order *little endian*, easier for arithmetic.
        num.reverse();

        BigNum { num, sign }
    }

    /// WARNING! Very basic naive random number generator below a given big
    /// number.
    pub fn gen_rand_num_below(target: &BigNum) -> BigNum {
        loop {
            let mut num = vec![0; target.num.len()];

            for i in 0..num.len() {
                num[i] = rand::thread_rng().gen_range(0, 10);
            }

            let mut below_num = BigNum { num, sign: false };

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
        let mut num_str: String = self.num.iter().map(|x| x.to_string()).rev().collect();

        // Check if the number is negative.
        if self.sign {
            num_str.insert(0, '-');
        }

        write!(f, "{}", num_str)
    }
}

impl Add for BigNum {
    type Output = BigNum;

    fn add(self, other: BigNum) -> BigNum {
        // TODO: rename using correct arithmetic terms.
        // TODO: refactor operands to big single characters.
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

        BigNum {
            num: result,
            sign: false,
        }
    }
}

impl Sub for BigNum {
    type Output = BigNum;

    fn sub(self, other: BigNum) -> BigNum {
        // Used to flag if the result will be negative.
        let mut sign: bool = false;

        // Operands for the subtraction.
        let minuend: BigDigit;
        let addend: BigDigit;

        let mut result: BigDigit = vec![];
        let mut carry = 0;

        // Assigning minuend and addend, helpful when flagging for negative
        // number.
        if self < other {
            sign = true;
            minuend = other.num;
            addend = self.num;
        } else {
            minuend = self.num;
            addend = other.num;
        }

        for i in 0..addend.len() {
            // Assign each number as minuend (m) and added (a).
            // m - a = r.
            let mut m = minuend[i as usize];
            let a = addend[i as usize];

            // The result at each column of subtraction.
            let mut column_result = 0;

            if m == a && carry > 0 || m < a && carry > 0 {
                m += 10;
                result.push((m - a) - carry);
                continue;
            }

            // Add 10 to enable subtraction of a lower value.
            if m < a {
                m += 10;
                result.push(m - a);
                carry = 1;
                continue;
            }

            // Result at column.
            if carry > 0 {
                column_result = (m - a) - carry;
            } else {
                column_result = m - a;
            }

            result.push(column_result);
            carry = 0;
        }

        // Sub the rest if there is a difference between small and big.
        for i in addend.len()..minuend.len() {
            result.push(minuend[i] - carry);
            carry = 0;
        }

        remove_leading_zeroes(&mut result);

        BigNum { num: result, sign }
    }
}

// TODO: LOOK UP how to test for errors.
// #[cfg(test)]
// mod init_tests {
//     use super::*;
//
//     #[test]
//     fn dec_str_1() {
//         let x = BigNum::from_dec_str("sfdafs");
//     }
//
// }

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

    #[test]
    fn subtraction_5() {
        let x = BigNum::from_dec_str("1238758592436584327503819247913286418235761302847321985648723569230814712309857312958613290846321904872310984732195847389256438275623014781239084731290847");
        let y = BigNum::from_dec_str("32481237549385701982745329084730921847193824712385618297563298174321894128356321987409312749031286583721640912387439201865091265019254");

        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("1238758592436584327471338010363900716253015973762591063801529744518429094012294014784291396717965582884901671983164560805534797363235575579373993466271593"));
    }

    #[test]
    fn subtration_6() {
        let x = BigNum::from_dec_str("23154213980470912384723014872301984732901847329014782309184732190487321098473219084703912847390218479301247891203857910246589127643091284730918472319084720470956812095");
        let y = BigNum::from_dec_str("4250102498509328140392147889321743982164125943275987342598723194873219847329847938214739218472138965382176423879648329746983217469382174683217946392817461987346193827");

        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("18904111481961584244330866982980240750737721385738794966586008995614101251143371146489173628918079513919071467324209580499605910173709110047700525926267258483610618268"));
    }

    #[test]
    fn subtraction_negative_1() {
        let x = BigNum::from_dec_str("100");
        let y = BigNum::from_dec_str("102");

        let result = x - y;

        // TODO: After updating initialising a negative num, update this test.
        assert_eq!(result.to_string(), "-2");
    }

    #[test]
    fn subtraction_negative_2() {
        let x = BigNum::from_dec_str("1");
        let y = BigNum::from_dec_str("10");

        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("-9"));
    }

    #[test]
    fn subtraction_negative_3() {
        let x = BigNum::from_dec_str(
            "11092582130948132095819287519023847329184739281472309847321522222222",
        );
        let y = BigNum::from_dec_str("481902347912387592138041235712098473291847398217439287409321847918275129835723190847312894071234");

        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("-481902347912387592138041235701005891160899266121619999890298000589090390554250880999991371849012"));
    }
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

    // #[test]
    // fn compare_negative_num_1() {
    //     let x = BigNum::from_dec_str("-1");
    //     let y = BigNum::from_dec_str("1");
    //
    //     assert!(x < y);
    // }
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
