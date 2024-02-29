require('d3')
require('tone')


// constants for rendering and playback
const staffMiddles = [200, 400];
const notesPerStaff = 8;
const staffLeft = 25;
const staffMargin = 40;
const lineSpacing = 20;
const noteSpacing = 70;
const noteWidth = 32;
const noteHeight = Math.round(noteWidth * 5/8);
const clefWidth = Math.round(0.68 * 4 * lineSpacing);
const ledgerMargin = 8;
const noteTiming = 0.3;
const noteImg = "https://uploads-ssl.webflow.com/5d88ada011bed54810655344/"
    + "5dd5689265518fb9e5a43148_Whole-note-musical-symbols-classical-music"
    + "-blog-semibreve-min.png"
const clefImg = "https://openclipart.org/image/800px/270451"


// get data from Forge
let cfDegrees = Cf0.degrees._tuples.map(tuple => Number(tuple._atoms[1]));
let cfMode = Number(Cf0.mode._tuples);

// convert scale degrees to pitches according to the mode, with C = 0
let noteNumbers = cfDegrees.map(degree => degree + cfMode);

// move notes up/down octaves so they're roughly centered around zero
let maxNote = Math.max.apply(Math, noteNumbers);
let minNote = Math.min.apply(Math, noteNumbers)
let middleNote = (maxNote + minNote) / 2;
let averageOctave = Math.round(middleNote / 7);
noteNumbers = noteNumbers.map(note => note - (averageOctave * 7));

// convert note numbers to note names (e.g. A4)
const NOTES = ["C", "D", "E", "F", "G", "A", "B"];
let noteNames = noteNumbers.map(note =>
    NOTES[mod(note, 7)] // pitch name
    + (Math.floor(note / 7) + 4) // octave number
);

// draw on svg (see function definitions below)
d3.selectAll("svg > *").remove();
staffMiddles.forEach(y => drawClef(staffLeft, y - (2 * lineSpacing)));
for (let i = 0; i < noteNumbers.length; i++) {
    drawNote(i, noteNumbers[i]);
}
staffMiddles.forEach(drawStaff);

// play sound
const synth = new tone.Synth().toDestination();
const now = tone.now();
for (let i = 0; i < noteNames.length; i++) {
    synth.triggerAttackRelease(noteNames[i], "8n", now + (i * noteTiming))
}


/**
 * Draws one staff using the rendering constants
 * @param {int} staffMiddle the y-coordinate of the middle line of the staff
 */
function drawStaff(staffMiddle) {
    const staffLength = (noteSpacing * (notesPerStaff - 1)) + noteWidth
        + (2 * staffMargin) + clefWidth;
    for (let i = -2; i <= 2; i++) {
        let y = staffMiddle + (i * lineSpacing);
        d3.select(svg).append("line")
            .attr("x1", staffLeft).attr("x2", staffLeft + staffLength)
            .attr("y1", y).attr("y2", y)
            .attr("stroke", "black");
    }
}

/**
 * Draws an alto clef at a given position
 * @param {int} x The x-coordinate for the left side of the clef
 * @param {int} y The y-coordinate for the top of the clef
 */
function drawClef(x, y) {
    const clefHeight = 4 * lineSpacing;
    d3.select(svg).append("image")
        .attr("x", x).attr("y", y)
        .attr("width", clefWidth).attr("height", clefHeight)
        .attr("href", clefImg);
}

/**
 * Draws a whole note at a given position
 * @param {int} measure the measure number (starting from 0)
 * @param {int} note the note number (C4 = 0)
 */
function drawNote(measure, note) {
    let measureOnStaff = measure % notesPerStaff;
    let staffNumber = Math.floor(measure / notesPerStaff);
    let staffMiddle = staffMiddles[staffNumber];
    let x = staffLeft + staffMargin + clefWidth
        + (measureOnStaff * noteSpacing);
    let y = staffMiddle - (note * lineSpacing / 2) - (noteHeight / 2);

    // Draw note
    d3.select(svg).append("image")
        .attr("x", x).attr("y", y)
        .attr("width", noteWidth).attr("height", noteHeight)
        .attr("href", noteImg);
    // Draw upper ledger lines
    for (let i = 6; i <= note; i += 2) {
        let ledgerY = staffMiddle - (i * lineSpacing / 2);
        drawLedger(x - ledgerMargin, x + noteWidth + ledgerMargin, ledgerY);
    }
    // Draw lower ledger lines
    for (let i = -6; i >= note; i -= 2) {
        let ledgerY = staffMiddle - (i * lineSpacing / 2);
        drawLedger(x - ledgerMargin, x + noteWidth + ledgerMargin, ledgerY);
    }
}

/**
 * Draws a ledger line with given boudns
 * @param {int} left The left edge of the line
 * @param {int} right The right edge of the line
 * @param {int} y The y-coordinate for the horizontal line
 */
function drawLedger(left, right, y) {
    d3.select(svg).append("line")
        .attr("x1", left).attr("x2", right).attr("y1", y).attr("y2", y)
        .attr("stroke", "black");
}

/**
 * Like the % operator but result is always positive
 * @param {int} p    @param {int} q    @returns {int}
 */
function mod(p, q) {
    return ((p % q) + q) % q;
}
