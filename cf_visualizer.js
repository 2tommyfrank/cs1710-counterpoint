require('d3')
require('tone')

d3.selectAll("svg > *").remove();

// constants for rendering and playback
const staffMiddles = [200, 400];
const notesPerStaff = 8;
const staffLeft = 25;
const staffMargin = 40;
const lineSpacing = 20;
const noteSpacing = 80;
const noteWidth = 32;
const noteHeight = Math.round(noteWidth * 5/8);
const clefWidth = Math.round(0.68 * 4 * lineSpacing);
const noteTiming = 0.3;

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
function mod(p, q) { // like the % operator but result is always positive
    return ((p % q) + q) % q;
}
let noteNames = noteNumbers.map(note =>
    NOTES[mod(note, 7)] // pitch name
    + (Math.floor(note / 7) + 4) // octave number
);

// calculate coordinates for each note
let noteCoords = Array(noteNumbers.length);
for (i = 0; i < noteNumbers.length; i++) {
    let note = noteNumbers[i];
    let staffNumber = Math.floor(i / notesPerStaff);
    let measureNumber = i % notesPerStaff;
    let staffMiddle = staffMiddles[staffNumber];
    noteCoords[i] = [
        staffLeft + staffMargin + clefWidth + (measureNumber * noteSpacing),
        staffMiddle - (note * lineSpacing / 2) - (noteHeight / 2)
    ]
}

function drawClef(x, y) {
    const clefHeight = 4 * lineSpacing;
    d3.select(svg).append("image")
        .attr("x", x).attr("y", y)
        .attr("width", clefWidth).attr("height", clefHeight)
        .attr("href", "https://openclipart.org/image/800px/270451");
}
staffMiddles.forEach(y => drawClef(staffLeft, y - (2 * lineSpacing)));

/**
 * Draws a whole note at a given position
 * @param {int} x the x-coordinate for the left side of the image
 * @param {int} y the y-coordinate for the top of the image
 */
function drawNote(x, y) {
    d3.select(svg).append("image")
        .attr("x", x).attr("y", y)
        .attr("width", noteWidth).attr("height", noteHeight)
        .attr("href", "https://uploads-ssl.webflow.com/5d88ada011bed54810655344/5dd5689265518fb9e5a43148_Whole-note-musical-symbols-classical-music-blog-semibreve-min.png");
}
noteCoords.forEach(coord => drawNote(coord[0], coord[1]));

/**
 * Draws one staff using the rendering constants
 * @param {int} staffMiddle the y-coordinate of the middle line of the staff
 */
function drawStaff(staffMiddle) {
    const staffLength = (noteSpacing * (notesPerStaff - 1)) + noteWidth
        + (2 * staffMargin) + clefWidth;
    for (i = -2; i <= 2; i++) {
        let y = staffMiddle + (i * lineSpacing);
        d3.select(svg).append("line")
            .attr("x1", staffLeft).attr("x2", staffLeft + staffLength)
            .attr("y1", y).attr("y2", y)
            .attr("stroke", "black");
    }
}
staffMiddles.forEach(drawStaff);

const synth = new tone.Synth().toDestination();

// play sound
const now = tone.now();
for (i = 0; i < noteNames.length; i++) {
    synth.triggerAttackRelease(noteNames[i], "8n", now + (i * noteTiming))
}
