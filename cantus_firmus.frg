#lang forge/bsl

// Cantus firmus
one sig Cf {
    mode: one Int,
    degrees: pfunc Int -> Int
}

fun intervalOf[i, j : Int] : Int {
    add[abs[subtract[j, i]], 1]
}

pred wellformed {
    Cf.mode >= 0
    Cf.mode <= 6
    some Cf.degrees[0]
    // all i: Int | i != 0 implies {
    //     some Cf.degrees[i] implies some Cf.degrees[subtract[i, 1]]
    // }
    isSeqOf[Cf.degrees, Int]
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

    //cannot be longer than 16 notes
    all i : Int | i > 15 implies {
        no Cf.degrees[i]
    }
}

//starts and ends on modal final
pred validStartEnd {
    seqFirst[Cf.degrees] = 0
    seqLast[Cf.degrees] = 0
}



pred validRange {
    all disj i, j: Int {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] <= 8
    }
    some disj i, j: Int {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] >= 5
    }   
}

pred cantusFirmus {
    wellformed
    validMode
    validLength
    validStartEnd
    validRange

}
run { cantusFirmus } for 5 Int
