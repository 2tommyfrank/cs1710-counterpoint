#lang forge/bsl

// Cantus firmus
one sig Cf {
    mode: one Int,
    degrees: pfunc Int -> Int
}

pred wellformed {
    Cf.mode >= 0
    Cf.mode <= 6
    some Cf.degrees[0]
    all i: Int | i != 0 implies {
        some Cf.degrees[i] implies some Cf.degrees[subtract[i, 1]]
    }
}

pred validMode {
    let F = 3, B = 6 {
        Cf.mode != F
        Cf.mode != B
    }
}

pred validLength {
    // assuming wellformed, there are notes at indices 0-7
    some Cf.degrees[7]
}

run { wellformed validMode validLength }
