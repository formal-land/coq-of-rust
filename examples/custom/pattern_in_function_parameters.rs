use std::convert::TryFrom;

fn sum((x, y): (i32, i32)) -> i32 {
    x + y
}

fn steps_between(&start: &char, &end: &char) -> Option<usize> {
    let start = start as u32;
    let end = end as u32;
    if start <= end {
        let count = end - start;
        if start < 0xD800 && 0xE000 <= end {
            usize::try_from(count - 0x800).ok()
        } else {
            usize::try_from(count).ok()
        }
    } else {
        None
    }
}
