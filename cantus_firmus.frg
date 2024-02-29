#lang forge/bsl

option run_sterling "cf_visualizer.js"

// A cantus firmus is a short musical line with one note per measure and in
// a particular mode.
one sig Cf {
    // 0 = Ionian, 1 = Dorian, 2 = Phrygian, 4 = Mixolydian, 5 = Aeolian
    mode: one Int,
    // The scale degree of each note in the cantus firmus. The input is the
    // measure number and the output is the pitch of that note relative
    // to the starting pitch. Positive is higher, negative is lower.
    degrees: pfunc Int -> Int
}

// Calculates the last measure of a CF; useful for bounding length.
fun lastMeasure: Int {
    max[{ i: Int | some Cf.degrees[i] }]
}

// Calculates the musical interval between two notes. Equal to the absolute
// difference between the pitches plus one.
fun intervalOf[i, j : Int] : Int {
    add[abs[subtract[j, i]], 1]
}

// Make sure the mode is meaningful and that Cf.degrees is a sequence of notes.
pred wellformed {
    Cf.mode >= 0
    Cf.mode <= 6
    some Cf.degrees[0]
    isSeqOf[Cf.degrees, Int]
}

// Make sure that the mode is not Lydian (3) or Locrian (6), invalid for CFs.
pred validMode {
    let F = 3, B = 6 {
        Cf.mode != F
        Cf.mode != B
    }
}

// CFs should be between 8 and 16 notes long.
pred validLength {
    lastMeasure >= 7
    lastMeasure <= 15
}

// The CF should start and end on the modal final (scale degree 0).
pred validStartEnd {
    seqFirst[Cf.degrees] = 0
    seqLast[Cf.degrees] = 0
}

// The range of notes in the CF should be between 5 and 8.
pred validRange {
    all disj i, j: Int {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] <= 8
        // no "negative" intervals from integer overflow
        intervalOf[Cf.degrees[i], Cf.degrees[j]] > 0
    }
    some disj i, j: Int {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] >= 5
    }
}

// The CF should step down from the penultimate note to the final note.
pred penultimateDescent {
    Cf.degrees[subtract[lastMeasure, 1]] = 1
}

//TODO
// The CF should have a climax note higher than all the others; this note
// should not be a seventh above the starting note to avoid too much tension.
pred validClimax {
    some i: Int | all j: Int | i != j implies {
        Cf.degrees[i] > Cf.degrees[j]
        Cf.degrees[i] != 6 // no seventh climax
    }
}

// Calculates Euclidean modulo (result always positive)
fun mod[a, p: Int]: Int {
    let rem = remainder[a, p] {
        rem >= 0 implies rem else add[p, rem]
    }
}

// Calculates whether two notes form a tritone, i.e. an augmented 4th or a
// diminished 5th. With only white notes, the only tritone is F - B.
pred tritone[pitch1, pitch2: Int] {
    let F = mod[subtract[3, Cf.mode], 7], B = mod[subtract[6, Cf.mode], 7] {
        (mod[pitch1, 7] = F and mod[pitch2, 7] = B) or
        (mod[pitch1, 7] = B and mod[pitch2, 7] = F)
    }
}

// The CF should not have a tritone, either immediately or separated by
// a run of ascending or descending notes. Tritones are too dissonant.
pred noTritones {
    no disj i, j: Int | {
        0 <= i
        i < j
        j <= lastMeasure
        tritone[Cf.degrees[i], Cf.degrees[j]]

        (all m: Int | (i <= m and m < j) implies {
            Cf.degrees[m] < Cf.degrees[add[m, 1]]
        })
        or
        (all m: Int | (i <= m and m < j) implies {
            Cf.degrees[m] > Cf.degrees[add[m, 1]]
        })
    }
}

// The CF also should not have repeated notes (unisons) or immediate sevenths.
pred noBadIntervals {
    all i : Int | let j = add[i, 1] {
        (i >= 0 and i < lastMeasure) implies {
            intervalOf[Cf.degrees[i], Cf.degrees[j]] != 1
            intervalOf[Cf.degrees[i], Cf.degrees[j]] != 7
        }
    }
}

// The CF should be "mostly" steps but also include at least one skip or leap.
pred mostlySteps {
    let numJumps = #{ i: Int | let j = add[i, 1] {
        i >= 0
        i < lastMeasure
        intervalOf[Cf.degrees[i], Cf.degrees[j]] > 2
    }} {
        numJumps < divide[lastMeasure, 2]
        numJumps > 0
    }
}

// The CF should not have consecutive two skips or leaps in the same direction.
pred noArpeggios {
    no i: Int | let j = add[i, 1], k = add[i, 2] {
        sign[subtract[Cf.degrees[i], Cf.degrees[j]]]
        = sign[subtract[Cf.degrees[j], Cf.degrees[k]]]
        intervalOf[Cf.degrees[i], Cf.degrees[j]] > 2
        intervalOf[Cf.degrees[j], Cf.degrees[k]] > 2
    }
}

// Includes all the above predicates
pred cantusFirmusLite {
    wellformed
    validMode
    validLength
    validStartEnd
    validRange
    penultimateDescent
    validClimax
    noTritones
    noBadIntervals
    mostlySteps
    noArpeggios
}

// The CF should not circle around the same note for too long, as this is
// too repetitive.
pred noCircling {
    no i: Int | let j = add[i, 2], k = add[i, 4] {
        i >= 0
        i <= subtract[lastMeasure, 4]
        Cf.degrees[i] = Cf.degrees[j]
        Cf.degrees[j] = Cf.degrees[k]
    }
}

// The CF should also not have three consecutive skips or leaps, even in
// alternating directions.
pred noTripleJump { // this is not track and field
    no i: Int | let j = add[i, 1], k = add[i, 2], m = add[i, 3] {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] > 2
        intervalOf[Cf.degrees[j], Cf.degrees[k]] > 2
        intervalOf[Cf.degrees[k], Cf.degrees[m]] > 2
    }
}

// This predicate combines all the other predicates to check that the cantus
// firmus follows all the rules.
pred cantusFirmus {
    cantusFirmusLite
    noCircling
    noTripleJump
}

// Finds a cantus firmus but potentially with circling or triple jumps. These
// CFs tend to be a little less aesthetically pleasing, indicating the
// importance of the last two predicates!
run { cantusFirmusLite } for 5 Int

// Finds an example of a cantus firmus
run { cantusFirmus } for 5 Int

// The above run statement tends to find cantus firmi that mostly go below the
// starting note and not above; this run statement checks that cantus firmi can
// go at least a fifth above the starting note and still be valid.
pred fifthAbove { some i: Int | Cf.degrees[i] >= 5 }
run { cantusFirmus fifthAbove } for 5 Int

// This example shows off ledger lines :)
inst ledgerLines {
    `Cf0.mode = 0
    `Cf0.degrees = // C C B A G A D E D C
    0->0 + 1->7 + 2->6 + 3->5 + 4->4 + 5->5 + 6->1 + 7->2 + 8->1 + 9->0
}
run { cantusFirmus } for 5 Int for ledgerLines
