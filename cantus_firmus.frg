#lang forge/bsl

// Cantus firmus
one sig Cf {
    mode: one Int,
    degrees: pfunc Int -> Int
}

// Tommy
fun lastMeasure: Int {
    max[{ i: Int | some Cf.degrees[i] }]
}

// Ethan
fun intervalOf[i, j : Int] : Int {
    add[abs[subtract[j, i]], 1]
}

// Tommy
pred wellformed {
    Cf.mode >= 0
    Cf.mode <= 6
    some Cf.degrees[0]
    // all i: Int | i != 0 implies {
    //     some Cf.degrees[i] implies some Cf.degrees[subtract[i, 1]]
    // }
    isSeqOf[Cf.degrees, Int]
}

// Ethan
pred validMode {
    let F = 3, B = 6 {
        Cf.mode != F
        Cf.mode != B
    }
}

// Ethan
pred validLength {
    lastMeasure >= 7
    lastMeasure <= 15
}

// Ethan
//starts and ends on modal final
pred validStartEnd {
    seqFirst[Cf.degrees] = 0
    seqLast[Cf.degrees] = 0
}

// Ethan
pred validRange {
    all disj i, j: Int {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] <= 8
    }
    some disj i, j: Int {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] >= 5
    }   
}

// Tommy
pred penultimateDescent {
    Cf.degrees[subtract[lastMeasure, 1]] = 1
}

// Ethan
pred validClimax {
    some i: Int | all j: Int | i != j implies {
        Cf.degrees[i] > Cf.degrees[j]
        Cf.degrees[i] != 6 // no seventh climax
    }
}

// Tommy
fun mod[a, p: Int]: Int {
    let rem = remainder[a, p] {
        rem >= 0 implies rem else add[p, rem]
    }
}

// Tommy
pred samePitch[pitch1, pitch2: Int] {
    mod[subtract[mod[pitch1, 7], mod[pitch2, 7]], 7] = 0
}

// Tommy
pred noTritones {
    let F = subtract[3, mode], B = subtract[6, mode] {
        no i: Int | let j = add[i, 1] {
            (samePitch[Cf.degrees[i], F] and samePitch[Cf.degrees[j], B]) or
            (samePitch[Cf.degrees[i], B] and samePitch[Cf.degrees[j], F])
        }
    }
}

// Ethan
pred badInterval {
    //there is a seventh
    some i : Int | {
        intervalOf[Cf.degrees[i], Cf.degrees[add[i, 1]]] = 7 or
        intervalOf[Cf.degrees[i], Cf.degrees[add[i, 1]]] = 1
    }

}

pred cantusFirmus {
    wellformed
    validMode
    validLength
    validStartEnd
    validRange
    penultimateDescent
    validClimax
    noTritones
    not badInterval
}

run { cantusFirmus } for 5 Int
