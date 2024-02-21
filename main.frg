#lang forge/bsl
open "cantus_firmus.frg"
open "counterpoint.frg"

sig Line {
    notes: pfunc Int -> Int
}

pred cantusFirmus[line: Line] {
}

pred counterpoint[cf: Line, counter: Line] {
}
