type Coordinate = [number, number];
type Direction = string;
type CoordinateDirectionPair = [Coordinate, Direction];

type Circuit = {
  name: string;
  input: CoordinateDirectionPair[];
  output: CoordinateDirectionPair[];
  content: string;
};

const circuits: Circuit[] = [
    {
        name: "select circuit",
        input: [],
        output: [],
        content: "!",
    },
    {
        name: "And gate - EW - N",
        input: [[[1,0],"W"],[[-1,0],"E"]],
        output: [[[0,-1],"N"]],
        content: `
o20$30b2o$31bo$31bobo5bo$32b2o4bobo$37bob2o15b2o$36b2ob2o16bo$37bob2o
16bobo$38bobo8b2o7b2o$18bo20bo9bobo$16b3o32bo$15bo35b2o$15b2o23bo$38bo
bo$39b2o$12b3o$12b3o$11bo3bo7bo$23b2o$10b2o3b2o5bobo8$55bo$10b2o41bobo
$11bo42b2o$8b3o$8bo24bo$33b3o$36bo$21b3o11b2o$21bo$22bo65b2o$88bobo$
88bo$38bo$37b3o$36b5o$35bobobobo$35b2o3b2o$121bo$121b3o$38bo85bo$37bob
o83b2o$37bo98b2o$38bo2bo94bo$41bo92bobo$33b2o5bo16b2o13b3o28b2o25bo3b
2o$o2bo28bo2bo5b3o13b2o13bo2bo27bobo23bobo$4bo29bo8bo28bo30bo25b2o$o3b
o26bo2bo37bo46bo8bo2bo$b4o68bobo43bobo6b2ob2o$31b2o31b2o53b2o7bo3bo12b
4o$63bobo63b3o13bo3bo$63bobob2o76bo$64bobobo54b2o21bo2bo$66bo57bo$54b
2obob2o4b2o54b3o$4b2o58b3o54bo$4b2o48bo5bo3b3o58bob2o$64b3o56b3ob2o2b
2o3b2o$19b2o34b2ob2o5b2o55bo8bo2bo2bo$20b2o35bo8bo5b3o43b2o3b3ob2o3b5o
$19bo44bobobo2bo2bo5b2o36bobo4bobo$31b2o30bobob2o5bo5b2o36bo6bobo3bob
2o$31b2o30bobo8bo51bo4b2obo$64b2o5bobo$83bo18b2o43bo$12bo17b3o27bo21bo
18bobo41b3o$2b2o3b2o3b2o4b2o10b3o21b3o4b2o19bo18bo42bo$11bobo4bobo32bo
3bo2b2o38b2o42b2o$3bo3bo10bo$4b3o45bo5bo19b2o3b2o$4b3o21b2o3b2o17b2o3b
2o22bo$29b5o40b2o2bo5bo$30b3o41bobo2b2ob2o58bo$7bo23bo35bobo4bo5bobo
58b3o$6b3o16b3o40b2o11bo51b2o5b5o$5bo3bo15bo42bo3bo8bo51bobo3bobobobo$
7bo18bo45b2o59bo5b2o3b2o$4bo5bo60bobo46bo$4bo5bo108b2o$5bo3bo69bo23b2o
13b2o4b2o2b2o12bo$6b3o69b3o22b3o11b3o4b2o2b2o11bobo$77bo3bo12b2o9b2obo
9b2o4b2o15bo$28b3o24b2o3b2o14bob3obo11bo5bo4bo2bo10b2o21bo2bo$56b5o3b
2o11b5o17bo5b2obo11bo24bo$28bobo25b2ob2o4b2o28bo3bo3b3o10bo27bo$27b5o
24b2ob2o3bo32bo5b2o9bobo28b3o$26b2o3b2o24b3o55b2o30bo$26b2o3b2o2$6b2o$
6b2o21bo101bo$27b2o30b3o61bo7b2o$59b3o62bo5bobo$26bo31bo3bo59b3o$57bo
5bo14b2o$27bo2bo27bo3bo15b2o$29b2o28b3o2$123b2o$124b2o$123bo$112b2o$
111bo3bo$110bo5bo7bo$100b2o8bo3bob2o4bobo$100b2o8bo5bo3b2o$60b2o49bo3b
o4b2o12b2o$60b2o50b2o6b2o12b2o$122bobo$124bo$60b2o$61bo$61bobo$62b2o
10$149bo!
`,
    },
    {
        name: "And gate - EN - E",
        input: [[[-1,0],"E"],[[0,1],"N"]],
        output: [[[1,0],"E"]],
        content: `
o57$47b2o$48bo$48bobo$49b2o$52b2o$52bobo$52bo8$o2$o$bo2$67b2o$67bobo$
67bo13$82b2o$82bobo$82bo13$97b2o$97bobo$97bo2$86b2o$85bo2bo$88bo$88bo$
86bobo11bo3b3o$86bobo11b2o2bo$87bo11bobo3bo3$84b2o3b2o$84bo5bo21bo2bo
8bo$112bo10bobo$85bo3bo2b2o14bo2bo3b2o5bo3b2o$86b3o4b2o10b4o3b2obobo4b
o3b2o3b2o$92bo11b4o14bo3b2o3b2o$97b2o5bo2bo8b2o5bobo$97b2o5b4o16bo$
105b4o$108bo2$89bo$87b2ob2o2$86bo5bo2$86b2obob2o9$88b2o$88b2o!
`,
    },
    {
        name: "And gate - ES - E",
        input: [[[-1,0],"E"],[[0,-1],"S"]],
        output: [[[1,0],"E"]],
        content: `
o3$117b2o$117b2o9$117bo$116b3o$115b5o$114b2o3b2o$115b5o$115bo3bo$116bo
bo$117bo3$119bo$117b2ob2o$112bo$111bo4bo5bo$111b3o$116b2obob2o$107b2o$
108bo$107b2o$105bobo3bo$104bo3b2obo$105bobob3o3$113bo5b2o$112b2o5b2o$
112bobo$97bo$96bo$96b3o$121bo7bo$120b4o5bobo$115b2o2bo2b2o8b2o$115b2o
2b2o11b2o4b2o$112b2o10bo7b2o4b2o$104b2o5b3o10bo4bobo$104b2o6b2o10bo4bo
$115b2o$115b2o4$82bo$81bo$81b3o13$67bo$o65bo$66b3o$o$bo11$52bo$51bo$
51b3o13$38b2o$39bo$36b3o$36bo!
`,
    },
    {
        name: "Or gate - EN - E",
        input: [[[-1,0],"E"],[[0,1],"N"]],
        output: [[[1,0],"E"]],
        content: `
o52$83b2o$83bo2bo$87bo9bobo$71bo15bo7bo3bo$68b4o15bo7bo$59bo7b4o12bo2b
o7bo4bo8b2o$58bobo6bo2bo12b2o10bo12b2o$57bo3b2o4b4o24bo3bo$43bo2b2o9bo
3b2o5b4o14bobo8bobo$41b3o2b2o9bo3b2o8bo14b2o$40bo17bobo26bo$40b2o17bo
31b2o9b2o$27b2o39bobo19bo2bo7bo2bo$28bo40b2o19b3o9b3o$28bobo38bo23b9o$
29b2o49bo11bo2b5o2bo$37b2o39b2o12b2o2b3o2b2o$36bo2bo39b2o$37b2o$o75bo
13bo2bo26bo2bo26bo$77b2o15bo29bo$o75b2o12bo3bo25bo3bo25bo$bo78b3o8b4o
26b4o26bo$40b2o40bo$40bo30bo9bo$41b3o26bobo$43bo14b2o10b2obo8bobo$36b
2obo18b2o10b2ob2o6bo2bo$27b2o3b2o2b2ob3o28b2obo6b2o10b2o$27bo2bo2bo8bo
27bobo5b2o3bo8b2o$28b5o3b2ob3o29bo8b2o5b2o$37bobo41bo2bo4bo$30b2obo3bo
bo42bobo$30bob2o4bo9$41b2o$39bo2bo42b2o$84bobo$38bo47bo2$39b2o$18b2o
21bo14bo$18b2o36b3o$59bo$38b2o3b2o13b2o$38b2o3b2o$39b5o$40bobo2$40b3o
2$18b3o49b2o$17bo3bo47bobo$16bo5bo48bo14b2o$16bo5bo63bobo$19bo18bo49bo
$17bo3bo15bo50b2o$18b3o16b3o$19bo23bo$42b3o$41b5o$16b3o21b2o3b2o$16b3o
9bobo37b2o15b2o$15bo3bo8bobo34bo3bo15bo$23bobo3bo34bobo2bobo11bobo$14b
2o3b2o3b2o16b3o19bobo3b2o11b2o$24bo17b3o10b2o5b3ob2o9bo$54bobo4bo14bob
o$56bo5b3ob2o8bobo$43b2o19bob2o9bo$43b2o2$61b2o2b2o$61bo2bobo$62bobo$
16b2o43b2ob2o13b2o$16b2o46bo14bo$64bobo13b3o$58b2o5b2o15bo$38bobo17bo$
39b2o6b2o7bobo$39bo7bobo6b2o$42b2o4b3o$41bo2bo4b3o$43bo4b3o$39bo7bobo$
38bob2o5b2o$38bo$37b2o!
`,
    },
    {
        name: "Not gate - E - E",
        input: [[[-1,0],"E"]],
        output: [[[1,0],"E"]],
        content: `
o49$30bo$28b4o$19b2o5b4ob2o9b2o$17bo2bo3bo3b2ob3o8b2o40b2o$8b2o6bo7bo
3b2ob2o49bo3bo$8b2o6bo6bo3b5o49bo5bo13b2o$16bo7b3o3bo42b2o5bo2bo3bo13b
2o4b3o$17bo2bo50bo2bo12bo10b2o6b5o22bo$19b2o37bobo9bo7bo7bo10b3o5bo3bo
bo19b3o$58bo3bo7bo6bo4bob2o12b2o6bo3b2o18bo$32bo29bo7bo7b2o9bobo9b2o
27b2o$33b2o13b2o8bo4bo7bo2bo14b2o10b2o$32b2o14b2o12bo10b2o15bo$58bo3bo
$58bobo8bobo21b2o9b2o$70b2o20bo2bo7bo2bo$70bo21b3o9b3o$83bo11b9o$39bob
o39b2o11bo2b5o2bo$40b2o40b2o10b2o2b3o2b2o$40bo$77bo$o77b2o10bo2bo26bo
2bo$77b2o15bo29bo$o89bo3bo25bo3bo$bo45bo43b4o26b4o$48b2o31b3o$47b2o21b
o12bo$70b4o8bo$60b2o9b4o10b2o$60b2o9bo2bo9bobo$65bo5b4o8b3o4b2ob3o$65b
o4b4o8b3o4bo2b4o$54bobo13bo12b3o4b2o$55b2o27bobo$55bo29b2o5$62bo$63b2o
$62b2o6$69bobo$70b2o$70bo5$77bo$78b2o$77b2o10$72b2o$73b2o$72bo$61b2o$
60bo3bo28b2o$59bo5bo7bo19bobo$49b2o8bo3bob2o4bobo21bo$49b2o8bo5bo3b2o
24b2o$60bo3bo4b2o12b2o$61b2o6b2o12b2o$71bobo$73bo!
`,
    },
    {
        name: "Turn clockwise",
        input: [[[-1,0],"E"]],
        output: [[[0,1],"S"]],
        content: `
o3$63b2o$63b2o9$60b2obob2o2$60bo5bo14b2o$81b2o$61b2ob2o$63bo2$83b2o12b
2o$97b2o3$66bo$60b3o4b2o10b2o3b2o$59bo3bo2b2o12b5o12b3o$80b2ob2o12b3o$
58bo5bo15b2ob2o11bo3bo$58b2o3b2o16b3o$95b2o3b2o2$61bo11bobo$60bobo11b
2o$62bo11bo$58bo36b3o$57bo12bo7bo20b2o$56bo4bo8b2o6bobo3bo14b2o15bobo$
58bo10bobo6b2o3b3o14b2o14bo3bo$55bo5bo20b5o11bobo5b2o12bo7bo$55bo5bo
19bobobobo10b2o6b2o8bo4bo4b4o$56bo3bo20b2o3b2o32bo4bobob2o9b2o$57b3o
56bo3bo3bo2bob3o8b2o$93b2o3b2o16bobo6bobob2o$62b2o20bo8b2o3b2o26b4o$
63b2o9bobo6bobo19bo22bo$62bo14bo5bobo9b3o8b2o9bo$67b2o8bo6bo10b3o7b2o
10bobo$66bobo5bo2bo5b2o11bo20b2o$66bobob2o3b3o5b2o$67bobobo11b2o$69bo$
60bo8b2o$59b3o7b3o38bo$59b3o7b3o23b2o12bo$69b3o23b2o12b3o$57b2o3b2o5b
2o$57b2o3b2o5bo$67bobobo$66bobob2o$60bo5bobo$59bobo5b2o$58b2o$58b2o$
58b3o$59bobo$60b2o2$95bo$94bo$94b3o$o2$o$bo$74bobo$77bo$77bo$74bo2bo$
75b3o4$80bo$79bo$79b3o26$52b2o$51bobo$51bo$50b2o!
`,
    },
    {
        name: "Turn anti-clockwise",
        input: [[[-1,0],"E"]],
        output: [[[0,-1],"N"]],
        content: `
o36$47b2o$48bo$48bobo$49b2o29$80b2o$80bobo$72b3o5bo$o71bo2bo$72bo$o71b
o$bo71bobo9$95b2o$57b2o36bobo$57b2o36bo3$55bo$56bo7b2o$56bo6bobo$63bob
ob2o$64bobobo$54b2o3b2o5bo$57bo7b2o$54bo5bo3b3o25b2o$55b2ob2o4b3o25bo
2bo$56bobo5b3o$57bo7b2o29bo13b2o$57bo8bo43bobo$64bobobo3b3o5b2o12b2o
14bo$63bobob2o3bo2bo4bobo10bo$63bobo6bo8b3o$64b2o6bo9b2o$73bobo6b2o6b
2o3b2o$59bobo18bobo7b2o3b2o32b2o$60b2o19bo9b5o3bo17b3o2bo5bo3bo$54b3o
3bo31bobo4b2o12bo3bo9bo5bo$53bo3bo40bobo10bobo4bo8bo3bob2o2b2o$52bo5bo
19b2o3b2o7b3o14b2o16bo5bo3b2o$52b2obob2o19b2o3b2o18b2o4b2o17bo3bo$103b
2o4b2o18b2o$67bo6b3o3b3o28bobo$68b2o4bo5b3o30bo$67b2o6bo5bo13bo$94bobo
$71b2o20bo3bo$58b2o12b2o20b3o$71bo20b2o3b2o2$78b3o$55b2o3b2o16b3o$55b
2o3b2o15bo3bo$56b5o3bo$57bobo4b2o10b2o3b2o$63bobo$57b3o3$94b2o$94b2o$
60bo$59bobo$58bo3bo$59b3o16b2o$57b2o3b2o14b2o11$60b2o$60b2o!
`,
    },
    {
        name: "Duplicate clockwise",
        input: [[[-1,0],"E"]],
        output: [[[1,0],"E"],[[0,1],"S"]],
        content: `
o2$88b2o$88b2o8$30b2o$30b2o2$70b2o14b2o3b2o$70b2o16b3o$32b2o53bo3bo$
88bobo$89bo3$28b2o3b2o$29b5o$29b2ob2o56b3o$29b2ob2o50bobo$30b3o34b2o3b
2o10b2o4bobo$85bo3b5o$68bo3bo15b2o3b2o$69b3o16b2o3b2o$69b3o2$78bo$35bo
40b2o12b2o$29bo3bobo41b2o$28b3o3b2o$27b5o36bo5bo6b2o$26bobobobo34b3o5b
o4b2o$26b2o3b2o34b3o3b3o6bo$40b3o$40bo24b2o3b2o19b2obob2o$29bo11bo23b
2o3b2o19bo5bo$28bobo7b4o50bo3bo$28bobo7bo2bo47bo3b3o$29bo10b2o26bo19b
2o$28b2o37bobo18bobo$28b2o36b2o6bobo$28b2o36b2o9bo6b2o$33b2o15bo15b3o
8bo6bobo$34b2o12bobo16bobo4bo2bo3b2obobo$33bo15b2o17b2o5b3o3bobobo$83b
o8bo$20b2o61b2o7bo$18bo2bo61b3o5bobo$17bo7b3o3bo51b3o4b2ob2o$9b2o6bo6b
o3b5o50b3o3bo5bo$9b2o6bo7bo3b2ob2o49b2o7bo$18bo2bo3bo3b2ob3o8b2o38bo5b
2o3b2o$20b2o5b4ob2o9b2o36bobobo$29b4o48b2obobo$31bo52bobo6bo$84b2o7bo$
94bo$65bo$63bobo$64b2o25b2o$91b2o6$o2$o$bo22$97b2o$97bo$98b3o$100bo!
`,
    },
    {
        name: "Duplicate anti-clockwise",
        input: [[[-1,0],"E"]],
        output: [[[1,0],"E"],[[0,-1],"N"]],
        content: `
o18$97b2o$97b2o8$97b3o$90bo5bo3bo$89b2o4bo5bo$89bobo3b2obob2o3$98bo$
97bobo$97bobo$98b3o$100b2o$100bo$101b3o$72b3o28bo$72bo2bo$72bo$72bo$
73bobo$86b3o$88bo$87bo13$71b3o$73bo$72bo8$72b3o$o71bo2bo$72bo$o71bo$bo
71bobo$56b3o$58bo$57bo2$24bo$23bobo$13b2o7bob2o10b2o$12bobo6b2ob2o10b
2o$2b2o7bo6b3obob2o$2b2o7bo2bo2bo2bo2bobo$11bo6b2o4bo63b2o$12bobo73b2o
$13b2o2$25bobo$26b2o13b3o37b2o$26bo16bo37bobo$21b2o19bo35b2obobo$21b2o
55bobobo$80bo$33b2o44b2o5b2obob2o$21b3o8bobo43b3o$21b3o7b3o44b3o5bo5bo
$78b3o$33b2o44b2o6b2ob2o$34bo37b3o5bo8bo$19b2o3b2o8bo30b2o5bo2bo2bobob
o$20b5o40b2o5bo5b2obobo$21b3o48bo8bobo$22bo50bobo5b2o$26b3o34bo$28bo
35bo21bo$27bo36bo19b2o4b3o$85b2o2bo3bo2$62b2o3b2o19bo5bo$65bo22b2o3b2o
$62bo5bo2b2o$23b3o37b2ob2o2bobo$64bobo5bo4bobo$23bobo39bo11b2o$22b5o
38bo8bo3bo$21b2o3b2o45b2o$21b2o3b2o45bobo2$67bo$24bo41b3o$25b2o38bo3bo
$64bob3obo14b2o3b2o$27bo37b5o11b2o3b5o$80b2o4b2ob2o$23bo2bo55bo3b2ob2o
$23b2o62b3o5$85b3o$85b3o$84bo3bo$67b2o14bo5bo$67b2o15bo3bo$85b3o10$85b
2o$85b2o!
`,
    },
    {
        name: "Wire - E - E",
        input: [[[-1,0],"E"]],
        output: [[[1,0],"E"]],
        content: "!",
    },
    {
        name: "Cross - EN - EN",
        input: [[[-1,0],"E"],[[0,1],"N"]],
        output: [[[1,0],"E"],[[0,-1],"N"]],
        content: "!",
    },
    {
        name: "Cross - ES - ES",
        input: [[[-1,0],"E"],[[0,-1],"S"]],
        output: [[[1,0],"E"],[[0,1],"S"]],
        content: "!",
    },
];

// Create the dropdown menu
const dropdown = document.createElement('select');
circuits.forEach((optionText) => {
    const option = document.createElement('option');
    option.value = optionText.name;
    option.textContent = optionText.name;
    dropdown.appendChild(option);
});
document.body.appendChild(dropdown);

const step_button = document.createElement('step');
step_button.textContent = 'step';
step_button.id = 'step_button';
document.body.appendChild(step_button);

const run_button = document.createElement('run');
run_button.textContent = 'run';
run_button.id = 'run_button';
document.body.appendChild(run_button);

const stop_button = document.createElement('stop');
stop_button.textContent = 'stop';
stop_button.id = 'stop_button';
document.body.appendChild(stop_button);

// New line
document.body.appendChild(document.createElement('br'));

// Set up the canvas
const canvas = document.createElement('canvas');
canvas.width = 170 * 5; // Grid size in pixels
canvas.height = 170 * 5;
document.body.appendChild(canvas);

const ctx = canvas.getContext('2d');
if (!ctx) {
    throw new Error('Failed to get the canvas rendering context');
}

// Parameters for the grid
const rows = 170; // Number of rows
const cols = 170; // Number of columns
const cellSize = canvas.width / cols; // Size of each cell
const updateInterval = 25; // Update interval in milliseconds
const black = '#000000';

// Create two grids (current and next state)
let grid: number[][] = [];
let nextGrid: number[][] = [];
let background: string[][] = [];
let inputs: CoordinateDirectionPair[] = [];
let outputs: CoordinateDirectionPair[] = [];
let stepCount: number = 0;
let allowRun: boolean = false;

// Function to reset grid
function resetGrids() {
    stepCount = 0;
    for (let row = 0; row < rows; row++) {
        for (let col = 0; col < cols; col++) {
            grid[row][col] = 0; 
            nextGrid[row][col] = 0; 
            background[row][col] = black;
        }
    }
}

// Initialize grids with zeros
for (let row = 0; row < rows; row++) {
    grid[row] = [];
    nextGrid[row] = [];
    background[row] = [];
    for (let col = 0; col < cols; col++) {
        grid[row][col] = 0; // Initially dead
        nextGrid[row][col] = 0; // Initially empty
        background[row][col] = black;
    }
}

// Function to initialize the grid from an RLE string
function initializeFromRLE(rle: string, startRow: number = 0, startCol: number = 0) {
    const lines = rle.split('\n');
    let row = startRow;
    let col = startCol;

    for (const line of lines) {
        // Skip comment lines by checking the first character directly
        if (line[0] === '#') continue;

        let count = 0;
        for (const char of line) {
            if (char >= '0' && char <= '9') {
                // Build the count from consecutive digits
                count = count * 10 + parseInt(char, 10);
            } else if (char === 'o') {
                // Alive cells
                if (count === 0) count = 1; // Ensure count is at least 1
                const aliveCount = count;
                for (let i = 0; i < aliveCount; i++) {
                    if (row < rows && col < cols) {
                        grid[row][col] = 1;
                    }
                    col++;
                }
                count = 0;
            } else if (char === 'b') {
                // Dead cells
                if (count === 0) count = 1; // Ensure count is at least 1
                const deadCount = count;
                col += deadCount;
                count = 0;
            } else if (char === '$') {
                // End of row
                if (count === 0) count = 1; // Ensure count is at least 1
                row += count;
                col = startCol;
                count = 0;
            }
        }
    }
}

// Draw the grid on the canvas
function drawGrid() {
    ctx.clearRect(0, 0, canvas.width, canvas.height); // Clear the canvas

    for (let row = 0; row < rows; row++) {
        for (let col = 0; col < cols; col++) {
            if (grid[row][col] === 1) {
                ctx.fillStyle = '#FFFFFF'; // Alive cells
            } else {
                ctx.fillStyle = background[row][col]; // Dead cells
            }
            ctx.fillRect(col * cellSize, row * cellSize, cellSize, cellSize);
            if (grid[row][col] === 1) {
                ctx.strokeStyle = '#CCCCCC'; // Grid lines
                ctx.strokeRect(col * cellSize, row * cellSize, cellSize, cellSize);
            }   
        }
    }
}

function toX(x:number) :number { return x+75+10; }
function toY(y:number) :number { return y+75+10; }

function deleteBox(x:number, y:number, w:number, h:number) {
    for (let i = 0; i < w; i++) {
        for (let j = 0; j < h; j++) {
            grid[toY(y+j)][toX(x+i)] = 0;
        }
    }
}

// Compute the next state of the grid
function computeNextState() {
    for (let row = 0; row < rows; row++) {
        for (let col = 0; col < cols; col++) {
            const aliveNeighbors = countAliveNeighbors(row, col);

            if (grid[row][col] === 1) {
                // Any live cell with 2 or 3 live neighbors survives
                nextGrid[row][col] = aliveNeighbors === 2 || aliveNeighbors === 3 ? 1 : 0;
            } else {
                // Any dead cell with exactly 3 live neighbors becomes alive
                nextGrid[row][col] = aliveNeighbors === 3 ? 1 : 0;
            }
        }
    }
    // Swap grids (nextGrid becomes the current grid)
    [grid, nextGrid] = [nextGrid, grid];

    if (stepCount == 59) {
        outputs.forEach((output) => {
            if (output[1] == "E" || output[1] == "W") {
                const x = output[0][0];
                const y = output[0][1];
                deleteBox(75*x-5, 75*y-5, 10, 10);
            }
        });
        inputs.forEach((input) => {
            if (input[1] == "E") {
                const x = input[0][0];
                const y = input[0][1];
                initializeFromRLE("$5bo2bo$9bo$5bo3bo$6b4o!",toY(75*y-5),toX(75*x-5));
            }
            if (input[1] == "W") {
                const x = input[0][0];
                const y = input[0][1];
                initializeFromRLE("5$4o$o3bo$o$bo2bo!",toY(75*y-5),toX(75*x-5));
            }
        });
    }   
    if (stepCount == 29) {
        outputs.forEach((output) => {
            if (output[1] == "N" || output[1] == "S") {
                const x = output[0][0];
                const y = output[0][1];
                deleteBox(75*x-5, 75*y-5, 10, 10);
            }
        });
        inputs.forEach((input) => {
            if (input[1] == "N") {
                const x = input[0][0];
                const y = input[0][1];
                initializeFromRLE("2b3o$bo2bo$4bo$4bo$bobo!",toY(75*y-5),toX(75*x-5));
            }
            if (input[1] == "S") {
                const x = input[0][0];
                const y = input[0][1];
                initializeFromRLE("5$6bobo$5bo$5bo$5bo2bo$5b3o!",toY(75*y-5),toX(75*x-5));
            }
        });
    }   
    stepCount = (stepCount+1) % 60;

}

// Count alive neighbors for a cell
function countAliveNeighbors(row: number, col: number): number {
    let count = 0;

    for (let dr = -1; dr <= 1; dr++) {
        for (let dc = -1; dc <= 1; dc++) {
            if (dr === 0 && dc === 0) continue; // Skip the cell itself
            const r = row + dr;
            const c = col + dc;

            // Check if the neighbor is within bounds and alive
            if (r >= 0 && r < rows && c >= 0 && c < cols && grid[r][c] === 1) {
                count++;
            }
        }
    }

    return count;
}

// Animation loop with controlled update interval
let lastUpdateTime = 0; // Timestamp of the last update
function gameLoop(timestamp: number) {
    if (timestamp - lastUpdateTime >= updateInterval) {
        computeNextState(); 
        drawGrid(); 
        lastUpdateTime = timestamp; // Update the timestamp
    }
    if (allowRun) {
        requestAnimationFrame(gameLoop); // Loop the animation
    }
}

function colourBox(x: number, y: number, w: number, h: number, colour: string) {
    for (let i = 0; i < w; i++) {
        for (let j = 0; j < h; j++) {
            const real_x = toX(x+i);
            const real_y = toY(y+j);
            if (0 <= real_y && real_y < rows && 0 <= real_x && real_x < cols) {
                background[real_y][real_x] = colour;
            }
        }
    }
}

function updateBackground() {
    colourBox(-75,-75,150,150,'#301934');
    outputs.forEach((output) => {
        const x = output[0][0];
        const y = output[0][1];
        colourBox(75*x-5, 75*y-5, 10, 10, '#483248');
    });
    inputs.forEach((input) => {
        const x = input[0][0];
        const y = input[0][1];
        colourBox(75*x-5, 75*y-5, 10, 10, '#483248');
    });
}

// Function to handle dropdown changes
function handleDropdownChange(event: Event) {
    const selectedValue = (event.target as HTMLSelectElement).value;
    resetGrids();
    circuits.forEach((circuit) => {
        if (circuit.name == selectedValue) {
            const rleContent = circuit.content;
            inputs = circuit.input;
            outputs = circuit.output;
            updateBackground();
            initializeFromRLE(rleContent, 10, 10); // Initialize grid with the RLE pattern
            drawGrid();     
            //requestAnimationFrame(gameLoop); // Start the simulation
        }
    });
}

dropdown.addEventListener('change', handleDropdownChange);
step_button.addEventListener('click', () => {
    computeNextState(); 
    drawGrid(); 
});
run_button.addEventListener('click', () => {
    allowRun = true;
    requestAnimationFrame(gameLoop);
});
stop_button.addEventListener('click', () => {
    allowRun = false;
});