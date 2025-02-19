// ************************************************************************* //
//  Circuits
// ************************************************************************* //

type Coordinate = [number, number];
type Direction = string;
type CoordinateDirectionPair = [Coordinate, Direction];

type Circuit = {
  name: string;
  input: CoordinateDirectionPair[];
  output: CoordinateDirectionPair[];
  height: number;
  width: number;
  content: string;
};

const circuits: Circuit[] = [
    {
        name: "And gate - EN - E",
        input: [[[-1,0],"E"],[[0,1],"N"]],
        output: [[[1,0],"E"]],
        height: 1,
        width: 1,
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
        height: 1,
        width: 1,
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
        name: "And gate - EW - N",
        input: [[[1,0],"W"],[[-1,0],"E"]],
        output: [[[0,-1],"N"]],
        height: 1,
        width: 1,
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
2obob2o4b2o54b3o$64b3o54bo$3b2o49bo5bo3b3o58bob2o$3b2o59b3o56b3ob2o2b
2o3b2o$19b2o34b2ob2o5b2o55bo8bo2bo2bo$20b2o35bo8bo5b3o43b2o3b3ob2o3b5o
$19bo44bobobo2bo2bo5b2o36bobo4bobo$63bobob2o5bo5b2o36bo6bobo3bob2o$30b
2o31bobo8bo51bo4b2obo$29bobo32b2o5bobo$28b3o52bo18b2o43bo$12bo15b2o30b
o21bo18bobo41b3o$4bo7b2o2b2o10b2o24b3o4b2o19bo18bo42bo$3b3o5bobo2bobo
10bobo21bo3bo2b2o38b2o42b2o$2b5o9bo13bo$b2o3b2o44bo5bo19b2o3b2o$2b5o
45b2o3b2o22bo$2b5o20b2o3b2o40b2o2bo5bo$3bo2bo20b2o3b2o40bobo2b2ob2o58b
o$3bo3bo59bobo4bo5bobo58b3o$7bo15b3o3b3o36b2o11bo51b2o5b5o$4b2obo15bo
5b3o36bo3bo8bo51bobo3bobobobo$6bo17bo5bo41b2o59bo5b2o3b2o$71bobo46bo$
119b2o$3b2o3b2o69bo23b2o13b2o4b2o2b2o12bo$3bo5bo68b3o22b3o11b3o4b2o2b
2o11bobo$77bo3bo12b2o9b2obo9b2o4b2o15bo$4bo3bo18b3o25b2o3b2o14bob3obo
11bo5bo4bo2bo10b2o21bo2bo$5b3o19b3o26b5o3b2o11b5o17bo5b2obo11bo24bo$
26bo3bo25b2ob2o4b2o28bo3bo3b3o10bo27bo$56b2ob2o3bo32bo5b2o9bobo28b3o$
25b2o3b2o25b3o55b2o30bo4$5b2o124bo$5b2o52b3o61bo7b2o$59b3o62bo5bobo$
58bo3bo59b3o$57bo5bo14b2o$58bo3bo15b2o$28b2o29b3o$28b2o$123b2o$124b2o$
123bo$112b2o$111bo3bo$110bo5bo7bo$100b2o8bo3bob2o4bobo$100b2o8bo5bo3b
2o$60b2o49bo3bo4b2o12b2o$60b2o50b2o6b2o12b2o$122bobo$124bo$60b2o$61bo$
61bobo$62b2o10$149bo!
`,
    },
    {
        name: "Or gate - EN - E",
        input: [[[-1,0],"E"],[[0,1],"N"]],
        output: [[[1,0],"E"]],
        height: 1,
        width: 1,
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
        height: 1,
        width: 1,
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
        name: "Half-adder - EE - ES",
        input: [[[-1,0],"E"],[[-1,2],"E"]],
        output: [[[3,0],"E"],[[2,3],"S"]],
        height: 2,
        width: 2,
        content: `
o23$101b2o$101b2o5$78b2o$78b2o2$100b3o$99bo3bo$79bo18bo5bo$78bobo17b2o
bob2o$77bo3bo$78b3o$76b2o3b2o18bo$100bobo$100bobo$101b2o$103bo$77bo24b
3o$77bo23bo3bo$77bob3o18bob3obo$96bo4b5o$82bo11b2o$79bob2o12b2o$79b2o
3$74b2o3b2o7bo114b2o$74b2o3b2o7b2o113bo2bo$75b5o6bobobo116bo9bobo$76bo
bo5b3o2b2o100bo15bo7bo3bo$188b4o15bo7bo$76b3o24b2o74bo7b4o12bo2bo7bo4b
o8b2o$103b2o73bobo6bo2bo12b2o10bo12b2o$177bo3b2o4b4o24bo3bo$163bo2b2o
9bo3b2o5b4o14bobo8bobo$161b3o2b2o9bo3b2o8bo14b2o$95bo64bo17bobo26bo$
76b2o15bobo64b2o17bo31b2o9b2o$76b2o16b2o51b2o39bobo19bo2bo7bo2bo$148bo
40b2o19b3o9b3o$148bobo38bo23b9o$149b2o49bo11bo2b5o2bo$157b2o39b2o12b2o
2b3o2b2o$156bo2bo39b2o$157b2o$o29bo2bo26bo2bo26bo2bo26bo2bo26bo2bo42bo
13bo2bo26bo2bo26bo2bo26bo$34bo29bo29bo29bo29bo42b2o15bo29bo29bo$o29bo
3bo25bo3bo25bo3bo25bo3bo25bo3bo41b2o12bo3bo25bo3bo25bo3bo25bo$bo29b4o
26b4o26b4o26b4o26b4o45b3o8b4o26b4o26b4o26bo$160b2o40bo$160bo30bo9bo$
110bo50b3o8bo17bobo$108bobo52bo9bo4b2o10b2obo8bobo$109b2o45b2obo11b3o
4b2o10b2ob2o6bo2bo$147b2o3b2o2b2ob3o28b2obo6b2o10b2o$147bo2bo2bo8bo27b
obo5b2o3bo8b2o32bo$148b5o3b2ob3o29bo8b2o5b2o37b3o$157bobo41bo2bo4bo39b
o$150b2obo3bobo42bobo43b2o$150bob2o4bo3$251bo$250b3o$250b3o2$125bo61bo
60b2o3b2o$123bobo62bo59b2o3b2o$124b2o60b3o$205b2o$204bobo$206bo43b2o2$
248b2o$248b2o3b2o$247bobo3bo$254b3o$256bo4$140bo61bo$138bobo62bo$139b
2o60b3o$190b2o$189bobo$191bo2$233bo$233b2o$232bobo6$155bo61bo$153bobo
62bo$154b2o60b3o19b2o$175b2o61bo$174bobo50bobo6bobo$176bo48bo3bo6b2o$
225bo$224bo4bo$225bo$219b2o4bo3bo$218bobo6bobo$218bo$217b2o3$170bo$
168bobo$169b2o$160b2o$159bobo$161bo10$104b2o79bo8bo$105bo77bobo6b3o18b
2o$105bobo10bo65b2o5bo21b2o$106b2o9b4o24b2o44b2o$116b2obobo22bobo$115b
3obo2bo23bo$116b2obob2o65b3o$117b4ob3o63b3o$109bobo6bo4bobo61bo3bo$
110b2o13bo60bo5bo$110bo14b2o60bo3bo$188b3o19b2obob2o2$210bo5bo14b2o$
231b2o$211b2ob2o$175bo37bo$173b2o$130b2o42b2o57b2o12b2o$129bobo54b2o
59b2o$93b3o35bo55bo$95bo88b3o$94bo89bo31bo$124bobo83b3o4b2o10b2o3b2o$
125b2o82bo3bo2b2o12b5o12b3o$125bo104b2ob2o12b3o$208bo5bo15b2ob2o11bo3b
o$154bo53b2o3b2o16b3o$154b3o88b2o3b2o$157bo$156b2o53bo11bobo$210bobo
11b2o$163bo48bo11bo$115b2o47bo43bo36b3o$114bobo45b3o42bo12bo7bo20b2o$
78b3o35bo89bo4bo8b2o6bobo3bo14b2o15bobo$80bo127bo10bobo6b2o3b3o14b2o
14bo3bo$79bo125bo5bo20b5o11bobo5b2o12bo7bo$139bobo16b3o44bo5bo19bobobo
bo10b2o6b2o8bo4bo4b4o$140b2o15bo3bo44bo3bo20b2o3b2o32bo4bobob2o9b2o$
140bo15bo5bo44b3o56bo3bo3bo2bob3o8b2o$156bo5bo80b2o3b2o16bobo6bobob2o$
159bo52b2o20bo8b2o3b2o26b4o$157bo3bo51b2o9bobo6bobo19bo22bo$158bo53bo
14bo5bobo9b3o8b2o9bo$159bo2bo54b2o8bo6bo10b3o7b2o10bobo$162bo53bobo5bo
2bo5b2o11bo20b2o$161bo16bo37bobob2o3b3o5b2o$100b2o60b3o14bo37bobobo11b
2o$99bobo62bo12b3o39bo$63b3o35bo108bo8b2o$65bo143b3o7b3o38bo$64bo144b
3o7b3o23b2o12bo$154bobo62b3o23b2o12b3o$155b2o50b2o3b2o5b2o$155bo51b2o
3b2o5bo$217bobobo$216bobob2o$210bo5bobo$209bobo5b2o$30bo103b2o44bo27b
2o$134b3o71b2o$30bo89bo15b2obo40bo12bo14b3o$85b2o31bobo4b3o8bo2bo5b2o
34bo12bo14bobo$84bobo30bobo16b2obo5b2o45b3o15b2o$48b3o35bo24b2o3bo2bo
7bo2b2o2b3o$50bo60b2o4bobo7bo3bo2b2o109bo$49bo68bobo6bo2bo113bo$120bo
8b2o38bobo72b3o$30bo2bo26bo2bo86bo2bo16b2o8bo2bo26bo2bo$34bo29bo71b4o
14bo15bo13bo29bo$30bo3bo25bo3bo70bo3bo10bo3bo25bo3bo25bo3bo$31b4o26b4o
74bo11b4o26b4o26b4o$90b2o43bo2bo85bobo$90b2o135bo$125b2o100bo$126b2o
17b2o7b2o68bo2bo$125bo19bo9bo30bo21bo16b3o$70b2o4bobo10b3o54b9o31b2o
21bo$69bobo17b3o44b2o5b3o2b5o2b3o23b2o4b2o18b3o$33b3o35bo4b5o7bo3bo42b
2o6bo2bo2b3o2bo2bo23b2o4b3o$35bo41b3o7bo5bo13bo9b2o18bo6b2o9b2o24b2o4b
2o41bo$13b2o19bo43b2o8bo3bo13bobo7b4o58b2o6b2o7b2o15b2o15bo$13b2o40bob
o31b3o7b2o4bob2o5b3o2bo2bobo52bobo6bo8bobo14bobo14b3o$54bo2bo3b2o36b2o
3b2ob2o9b2o2bo2bo25bo25bo19bo16bo$53b2o5b3ob2o2b2o35bob2o6bo9b2o17b2ob
o3b4o21b2o19b2o15b2o$13b3o29b2o4b2o3bo3bo3bo3bobo15bo19bobo5bo8bo3b2o
9b2o2b2obobo4b4o5b2o$13b3o29b2o6b2o5bobo8bo13b2o20bo6bo10b2o10bobo2b2o
bob2o3bo2bo5b2o$40b2o12bo2bo2b2o6bo2bo7b2o4bobo34bo2bo10b3o8b2o3b4o$
25bo14b2o13bobo13bo7b2o41bobo10b3o8b2o3b4o$22b2o44bobo65b3o12bo$11b2o
3b2o7bo42b2o67bobo$12b5o4bo4bo111b2o$13b3o6bob3o$14bo8b2o2bo12bo$18b3o
3b3o3bo9bo47bo$20bo4b2o2b2o8bobo45b3o$19bo9bobo6b2ob2o43b5o$37bo5bo41b
obobobo$40bo44b2o3b2o$37b2o3b2o2$88bo$15b3o18b3o48bobo$35b2obo48bobo$
15bobo17b2o51bo$14b5o17b2o50b2o$13b2o3b2o17bobo48b2o$13b2o3b2o17bo2b2o
46b2o$202b2o$201bobo$16bo184bo$17b2o181b2o2$19bo16b5o$35bob3obo$15bo2b
o17bo3bo$15b2o20b3o$38bo4$38b2o$38b2o!
`,
    },
    {
        name: "Half-adder - EE - EE",
        input: [[[-1,0],"E"],[[-1,2],"E"]],
        output: [[[3,0],"E"],[[3,2],"E"]],
        height: 2,
        width: 2,
        content: `
o23$101b2o$101b2o5$78b2o$78b2o2$100b3o$99bo3bo$79bo18bo5bo$78bobo17b2o
bob2o$77bo3bo$78b3o$76b2o3b2o18bo$100bobo$100bobo$101b2o$103bo$77bo24b
3o$77bo23bo3bo$77bob3o18bob3obo$96bo4b5o$82bo11b2o$79bob2o12b2o$79b2o
3$74b2o3b2o7bo114b2o$74b2o3b2o7b2o113bo2bo$75b5o6bobobo116bo9bobo$76bo
bo5b3o2b2o100bo15bo7bo3bo$188b4o15bo7bo$76b3o24b2o74bo7b4o12bo2bo7bo4b
o8b2o$103b2o73bobo6bo2bo12b2o10bo12b2o$177bo3b2o4b4o24bo3bo$163bo2b2o
9bo3b2o5b4o14bobo8bobo$161b3o2b2o9bo3b2o8bo14b2o$95bo64bo17bobo26bo$
76b2o15bobo64b2o17bo31b2o9b2o$76b2o16b2o51b2o39bobo19bo2bo7bo2bo$148bo
40b2o19b3o9b3o$148bobo38bo23b9o$149b2o49bo11bo2b5o2bo$157b2o39b2o12b2o
2b3o2b2o$156bo2bo39b2o$157b2o$o29bo2bo26bo2bo26bo2bo26bo2bo26bo2bo42bo
13bo2bo26bo2bo26bo2bo26bo$34bo29bo29bo29bo29bo42b2o15bo29bo29bo$o29bo
3bo25bo3bo25bo3bo25bo3bo25bo3bo41b2o12bo3bo25bo3bo25bo3bo25bo$bo29b4o
26b4o26b4o26b4o26b4o45b3o8b4o26b4o26b4o26bo$160b2o40bo$160bo30bo9bo$
110bo50b3o8bo17bobo$108bobo52bo9bo4b2o10b2obo8bobo$109b2o45b2obo11b3o
4b2o10b2ob2o6bo2bo$147b2o3b2o2b2ob3o28b2obo6b2o10b2o$147bo2bo2bo8bo27b
obo5b2o3bo8b2o32bo$148b5o3b2ob3o29bo8b2o5b2o37b3o$157bobo41bo2bo4bo39b
o$150b2obo3bobo42bobo43b2o$150bob2o4bo3$251bo$250b3o$250b3o2$125bo61bo
60b2o3b2o$123bobo62bo59b2o3b2o$124b2o60b3o$205b2o$204bobo$206bo43b2o2$
248b2o$248b2o3b2o$247bobo3bo$254b3o$256bo4$140bo61bo$138bobo62bo$139b
2o60b3o$190b2o$189bobo$191bo2$233bo$233b2o$232bobo6$155bo61bo$153bobo
62bo$154b2o60b3o19b2o$175b2o61bo$174bobo50bobo6bobo$176bo48bo3bo6b2o$
225bo$224bo4bo$225bo$219b2o4bo3bo$218bobo6bobo$218bo$217b2o3$170bo$
168bobo$169b2o$160b2o$159bobo$161bo10$104b2o79bo8bo$105bo77bobo6b3o$
105bobo10bo65b2o5bo$106b2o9b4o24b2o44b2o$116b2obobo22bobo$115b3obo2bo
23bo$116b2obob2o65b3o$117b4ob3o63b3o$109bobo6bo4bobo61bo3bo$110b2o13bo
60bo5bo$110bo14b2o60bo3bo$188b3o5$175bo$173b2o$130b2o42b2o$129bobo54b
2o$93b3o35bo55bo$95bo88b3o$94bo89bo$124bobo$125b2o$125bo2$154bo$154b3o
$157bo$156b2o2$163bo$115b2o47bo$114bobo45b3o$78b3o35bo$80bo$79bo$139bo
bo16b3o$140b2o15bo3bo$140bo15bo5bo$156bo5bo$159bo$157bo3bo$158bo$159bo
2bo$162bo$161bo16bo$100b2o60b3o14bo$99bobo62bo12b3o$63b3o35bo$65bo$64b
o$154bobo$155b2o$155bo5$30bo103b2o44bo$134b3o$30bo89bo15b2obo40bo12bo$
85b2o31bobo4b3o8bo2bo5b2o34bo12bo$84bobo30bobo16b2obo5b2o45b3o$48b3o
35bo24b2o3bo2bo7bo2b2o2b3o$50bo60b2o4bobo7bo3bo2b2o$49bo68bobo6bo2bo$
120bo8b2o38bobo$30bo2bo26bo2bo86bo2bo16b2o8bo2bo26bo2bo$34bo29bo71b4o
14bo15bo13bo29bo$30bo3bo25bo3bo70bo3bo10bo3bo25bo3bo25bo3bo$31b4o26b4o
74bo11b4o26b4o26b4o$90b2o43bo2bo$90b2o$125b2o$126b2o17b2o7b2o$125bo19b
o9bo30bo21bo$70b2o4bobo10b3o54b9o31b2o21bo$69bobo17b3o44b2o5b3o2b5o2b
3o23b2o4b2o18b3o$33b3o35bo4b5o7bo3bo42b2o6bo2bo2b3o2bo2bo23b2o4b3o$35b
o41b3o7bo5bo13bo9b2o18bo6b2o9b2o24b2o4b2o$13b2o19bo43b2o8bo3bo13bobo7b
4o58b2o6b2o7b2o15b2o$13b2o40bobo31b3o7b2o4bob2o5b3o2bo2bobo52bobo6bo8b
obo14bobo$54bo2bo3b2o36b2o3b2ob2o9b2o2bo2bo25bo25bo19bo16bo$53b2o5b3ob
2o2b2o35bob2o6bo9b2o17b2obo3b4o21b2o19b2o15b2o$13b3o29b2o4b2o3bo3bo3bo
3bobo15bo19bobo5bo8bo3b2o9b2o2b2obobo4b4o5b2o$13b3o29b2o6b2o5bobo8bo
13b2o20bo6bo10b2o10bobo2b2obob2o3bo2bo5b2o$40b2o12bo2bo2b2o6bo2bo7b2o
4bobo34bo2bo10b3o8b2o3b4o$25bo14b2o13bobo13bo7b2o41bobo10b3o8b2o3b4o$
22b2o44bobo65b3o12bo$11b2o3b2o7bo42b2o67bobo$12b5o4bo4bo111b2o$13b3o6b
ob3o$14bo8b2o2bo12bo$18b3o3b3o3bo9bo47bo$20bo4b2o2b2o8bobo45b3o$19bo9b
obo6b2ob2o43b5o$37bo5bo41bobobobo$40bo44b2o3b2o$37b2o3b2o2$88bo$15b3o
18b3o48bobo$35b2obo48bobo$15bobo17b2o51bo$14b5o17b2o50b2o$13b2o3b2o17b
obo48b2o$13b2o3b2o17bo2b2o46b2o$202b2o$201bobo$16bo184bo$17b2o181b2o2$
19bo16b5o$35bob3obo$15bo2bo17bo3bo$15b2o20b3o$38bo4$38b2o$38b2o!
`,
    },
    {
        name: "Turn clockwise",
        input: [[[-1,0],"E"]],
        output: [[[0,1],"S"]],
        height: 1,
        width: 1,
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
        height: 1,
        width: 1,
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
        height: 1,
        width: 1,
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
        height: 1,
        width: 1,
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
        height: 1,
        width: 1,
        content: "!",
    },
    {
        name: "Slow wire - E - E",
        input: [[[-1,0],"E"]],
        output: [[[7,0],"E"]],
        height: 1,
        width: 4,
        content: `
o5$87bo49bo49bo49bo49bo49bo49bo49bo49bo49bo$87b3o47b3o9bo37b3o47b3o47b
3o9bo37b3o47b3o47b3o9bo37b3o47b3o$90bo7b2o40bo8bo40bo7b3o39bo7b2o40bo
8bo40bo7b3o39bo7b2o40bo8bo40bo7b3o39bo7b2o$89bo9b2obo36b2o7bob2obo35b
2o11bo36bo9b2obo36b2o7bob2obo35b2o11bo36bo9b2obo36b2o7bob2obo35b2o11bo
36bo9b2obo$89bo3bo5b6o48bo45bo2bobo34bo3bo5b6o48bo45bo2bobo34bo3bo5b6o
48bo45bo2bobo34bo3bo5b6o$93bo10bo39bo5bo3bo88bo10bo39bo5bo3bo88bo10bo
39bo5bo3bo88bo10bo$95bo3b3ob3o37bobo4bo2b2o45b4obo39bo3b3ob3o37bobo4bo
2b2o45b4obo39bo3b3ob3o37bobo4bo2b2o45b4obo39bo3b3ob3o$89bo5bo5bo3bo37b
o2bo3bo4bo37b2ob2o3b3o2bo32bo5bo5bo3bo37bo2bo3bo4bo37b2ob2o3b3o2bo32bo
5bo5bo3bo37bo2bo3bo4bo37b2ob2o3b3o2bo32bo5bo5bo3bo$90bo4bo8b2o38b2o6bo
b2o37bo2bo7bo35bo4bo8b2o38b2o6bob2o37bo2bo7bo35bo4bo8b2o38b2o6bob2o37b
o2bo7bo35bo4bo8b2o$92bo12b2o87b2o8bo2bo34bo12b2o87b2o8bo2bo34bo12b2o
87b2o8bo2bo34bo12b2o$106b2o48b2o49bo48b2o48b2o49bo48b2o48b2o49bo48b2o$
106bo49bo49bo49bo49bo49bo49bo49bo49bo49bo$98bo8b3o47b3o47b3o38bo8b3o
47b3o47b3o38bo8b3o47b3o47b3o38bo8b3o$96bobo10bo29b2o18bo49bo36bobo10bo
29b2o18bo49bo36bobo10bo29b2o18bo49bo36bobo10bo$97b2o41b2o105b2o41b2o
105b2o41b2o105b2o$115b2o22bo25b2o48b2o48b2o22bo25b2o48b2o48b2o22bo25b
2o48b2o48b2o$115bo49bo49bo49bo49bo49bo49bo49bo49bo49bo$113bobo37bo9bob
o47bobo47bobo37bo9bobo47bobo47bobo37bo9bobo47bobo47bobo$84b2o27b2o36bo
bo9b2o48b2o19b2o27b2o36bobo9b2o48b2o19b2o27b2o36bobo9b2o48b2o19b2o27b
2o$85b2o65b2o81b2o65b2o81b2o65b2o81b2o$84bo149bo149bo149bo$159b2o47b2o
99b2o47b2o99b2o47b2o$109b3o46bo2bo45bobo49b3o46bo2bo45bobo49b3o46bo2bo
45bobo49b3o$109bo48bobo18b2o26bobo49bo48bobo18b2o26bobo49bo48bobo18b2o
26bobo49bo$109bo49bo20b2o26b2o49bo49bo20b2o26b2o49bo49bo20b2o26b2o49bo
$102bobo74bo28b2o42bobo74bo28b2o42bobo74bo28b2o42bobo$102b2o10bo49bo
48bo38b2o10bo49bo48bo38b2o10bo49bo48bo38b2o10bo$103bo8bobo45bob3o49b2o
37bo8bobo45bob3o49b2o37bo8bobo45bob3o49b2o37bo8bobo$110bo3bo9b2o34bob
2o45b3obo46bo3bo9b2o34bob2o45b3obo46bo3bo9b2o34bob2o45b3obo46bo3bo$
109b2o14b2o32b2obo50bo45b2o14b2o32b2obo50bo45b2o14b2o32b2obo50bo45b2o$
109b2ob2o10bo22bobo12b2o44bo50b2ob2o10bo22bobo12b2o44bo50b2ob2o10bo22b
obo12b2o44bo50b2ob2o$109b2o36b2o11bobo47bob2o45b2o36b2o11bobo47bob2o
45b2o36b2o11bobo47bob2o45b2o$107b2o3bo35bo9bob3o45bob2o45b2o3bo35bo9bo
b3o45bob2o45b2o3bo35bo9bob3o45bob2o45b2o3bo$69b2o39bo46b4o47b2o9b2o39b
o46b4o47b2o9b2o39bo46b4o47b2o9b2o39bo$70b2o33bo3bo45b3o47b2o13b2o33bo
3bo45b3o47b2o13b2o33bo3bo45b3o47b2o13b2o33bo3bo$69bo34bob2o46bobo35bob
o9bobo12bo34bob2o46bobo35bobo9bobo12bo34bob2o46bobo35bobo9bobo12bo34bo
b2o$104bo49bo37b2o10bo49bo49bo37b2o10bo49bo49bo37b2o10bo49bo$103b2o48b
2o38bo9b2o48b2o48b2o38bo9b2o48b2o48b2o38bo9b2o48b2o$164b2o148b2o148b2o
$165b2o148b2o148b2o$87bobo74bo72bobo74bo72bobo74bo72bobo$87b2o148b2o
148b2o148b2o$88bo149bo149bo149bo$109b2o148b2o148b2o$110b2o148b2o148b2o
$109bo22bobo124bo22bobo124bo22bobo$132b2o148b2o148b2o$133bo149bo149bo
136bobo$54b2o148b2o148b2o148b2o63bo2bo$55b2o148b2o148b2o148b2o61b2o10b
o6bo$54bo122bobo24bo122bobo24bo122bobo24bo53bo7b2o3bo8bo5bobo$177b2o
148b2o148b2o79bobo7b2o9bo6b2obo$178bo149bo149bo62bo17bobo7bo2bo2b2o9b
2ob2o3b2o$149b2o148b2o148b2o64bo25b2o16bo2bo7bobo2bo2b3o5b2obo4b2o$
150b2o148b2o148b2o63b3o18b2o4b2o15bobo13b4o7bobo$23bo2b2o44bobo74bo72b
obo74bo72bobo74bo68bo3bobo7b2o2b2o4b3o13bobo15b2o9bo$21b3o2b2o44b2o
148b2o148b2o143b2o3b2o8b2o2b2o4b2o7bobo4bo$20bo52bo149bo149bo148b2o17b
2o9b2o$20b2o72b2o148b2o148b2o145bo10bo24b2o9b2o$7b2o86b2o148b2o148b2o
123b2o47bo6bo2bo7bo2bo$8bo85bo22bobo124bo22bobo124bo22bobo147b2o7b3o9b
3o$8bobo106b2o148b2o148b2o149b2o9b9o$9b2o107bo149bo149bo159bo2b5o2bo$
17bo21b2o148b2o148b2o148b2o26b2o3b2o35bo18b2o2b3o2b2o$17b2o21b2o148b2o
148b2o148b2o25b2o3b2o36b2o$18bo20bo122bobo24bo122bobo24bo122bobo24bo
69b2o$o2bo158b2o148b2o148b2o55b3o48bo2bo$4bo22bo135bo149bo149bo55b3o
52bo$o3bo8bo14bo105b2o148b2o148b2o84bo49bo3bo$b4o7bobo11b3o17bo88b2o
148b2o148b2o134b4o$15bo4b2o22b3o10bobo74bo72bobo74bo72bobo74bo$12bo2bo
4bo22bo13b2o148b2o148b2o193b2o$13b3o5b3o19b2o13bo149bo149bo158b2o31bo
3bo5bo2b3o$23bo18b2o35b2o148b2o148b2o137bo25b2o3bo5bo9bo3bo$16b2obo11b
2o8b2o37b2o148b2o148b2o133b3o26b2o2b2obo3bo8bo4bobo$7b2o3b2o2b2ob3o8bo
2bo4bo3bo36bo22bobo124bo22bobo124bo22bobo110bo33bo5bo16b2o4b2o$7bo2bo
2bo8bo7bobo3b3ob3o59b2o148b2o148b2o146bo3bo17b2o4b2o$8b5o3b2ob3o9bo9bo
61bo149bo149bo148b2o18b2o$17bobo16b6o132b2o148b2o148b2o93bobo11b2o$10b
2obo3bobo6b2o8b2obo135b2o148b2o148b2o92bo12bobo$10bob2o4bo8bo7b2o110bo
bo24bo122bobo24bo122bobo24bo109bo$24b3o120b2o148b2o148b2o$24bo123bo
149bo149bo$119b2o148b2o148b2o$120b2o148b2o148b2o$42bobo74bo72bobo74bo
72bobo74bo$42b2o148b2o148b2o$43bo149bo149bo$64b2o148b2o148b2o184bo$65b
2o148b2o148b2o184bo$64bo22bobo124bo22bobo124bo22bobo159b3o$87b2o148b2o
148b2o$88bo149bo149bo$159b2o148b2o148b2o$160b2o148b2o148b2o$132bobo24b
o122bobo24bo122bobo24bo$132b2o148b2o148b2o$133bo149bo149bo145b2o$104b
2o148b2o148b2o172bo2bo$105b2o148b2o148b2o171bo$27bobo74bo72bobo74bo72b
obo74bo173bo$27b2o148b2o148b2o231b3o3bo11bobo$28bo149bo149bo233bo2b2o
11bobo$9b2o38b2o8b2o48b2o48b2o38b2o8b2o48b2o48b2o38b2o8b2o48b2o150bo3b
obo11bo$10bo39b2o8bo49bo49bo39b2o8bo49bo49bo39b2o8bo49bo$10bob2o2bo32b
o10bobo9bobo35bobo47bob2o2bo32bo10bobo9bobo35bobo47bob2o2bo32bo10bobo
9bobo35bobo$11bo5bo43b2o9b2o37b2o48bo5bo43b2o9b2o37b2o48bo5bo43b2o9b2o
37b2o163b2o3b2o$73bo149bo149bo168bo8bo2bo21bo5bo$18bo125b2o22bo125b2o
22bo125b2o95bobo10bo$13b2o50b2o49b2o27b2o16b2o50b2o49b2o27b2o16b2o50b
2o49b2o27b2o92b2o3bo5b2o3bo2bo14b2o2bo3bo$64bo2bo48bobo25bo69bo2bo48bo
bo25bo69bo2bo48bobo25bo89b2o3b2o3bo4bobob2o3b4o10b2o4b3o$15b3o47bobo
50bo46b3o47bobo50bo46b3o47bobo50bo115b2o3b2o3bo14b4o11bo$22bo43bo49b2o
54bo43bo49b2o54bo43bo49b2o123bobo5b2o8bo2bo5b2o$23bo65b2o25bo56bo65b2o
25bo56bo65b2o25bo125bo16b4o5b2o$11bo9b3o38bo27b2o19bo49bo9b3o38bo27b2o
19bo49bo9b3o38bo27b2o19bo146b4o$11b3obo44b2o27bo21bobo47b3obo44b2o27bo
21bobo47b3obo44b2o27bo21bobo144bo$12b2obo46bob3o44bo3bo46b2obo46bob3o
44bo3bo46b2obo46bob3o44bo3bo$13bob2o45bo14bo37b2o46bob2o45bo14bo37b2o
46bob2o45bo14bo37b2o160bo$12b2o20b2o31bo10bo33b2ob2o45b2o20b2o31bo10bo
33b2ob2o45b2o20b2o31bo10bo33b2ob2o158b2ob2o$13bobo19b2o9bo15b2obo10b3o
17bo18b2o29bo16bobo19b2o9bo15b2obo10b3o17bo18b2o29bo16bobo19b2o9bo15b
2obo10b3o17bo18b2o29bo$13b3obo16bo9b3o17b2obo26b3o16bo3b2o25b3o16b3obo
16bo9b3o17b2obo26b3o16bo3b2o25b3o16b3obo16bo9b3o17b2obo26b3o16bo3b2o
25b3o127bo5bo$15b4o24bo22b2o25bo21bo27bo21b4o24bo22b2o25bo21bo27bo21b
4o24bo22b2o25bo21bo27bo$18b3o23bo24b2o22b2o21bo3bo22b2o23b3o23bo24b2o
22b2o21bo3bo22b2o23b3o23bo24b2o22b2o21bo3bo22b2o129b2obob2o$19bobo19bo
2bo24bobo20b2o24b2obo9b2o36bobo19bo2bo24bobo20b2o24b2obo9b2o36bobo19bo
2bo24bobo20b2o24b2obo9b2o$21bo19bo29bo9b2o8b2o28bo8bo2b2o4bob2o28bo19b
o29bo9b2o8b2o28bo8bo2b2o4bob2o28bo19bo29bo9b2o8b2o28bo8bo2b2o4bob2o$
21b2o8b3o4b3o2bo27b2o7bo2bo4bo3bo28b2o7b5o2bo4bo28b2o8b3o4b3o2bo27b2o
7bo2bo4bo3bo28b2o7b5o2bo4bo28b2o8b3o4b3o2bo27b2o7bo2bo4bo3bo28b2o7b5o
2bo4bo$31bo5b4obo37bobo3b3ob3o44bo2b2o39bo5b4obo37bobo3b3ob3o44bo2b2o
39bo5b4obo37bobo3b3ob3o44bo2b2o$31bo49bo9bo45bo3bo39bo49bo9bo45bo3bo
39bo49bo9bo45bo3bo$36bo2bobo44b6o48bo45bo2bobo44b6o48bo45bo2bobo44b6o
48bo$26b2o11bo36b2o8b2obo36b2o7bob2obo35b2o11bo36b2o8b2obo36b2o7bob2ob
o35b2o11bo36b2o8b2obo36b2o7bob2obo$27bo7b3o39bo7b2o40bo8bo40bo7b3o39bo
7b2o40bo8bo40bo7b3o39bo7b2o40bo8bo$24b3o47b3o47b3o9bo37b3o47b3o47b3o9b
o37b3o47b3o47b3o9bo140b2o$24bo49bo49bo49bo49bo49bo49bo49bo49bo152b2o!
`,
    },
    {
        name: "Cross - EN - EN",
        input: [[[-1,0],"E"],[[0,1],"N"]],
        output: [[[1,0],"E"],[[0,-1],"N"]],
        height: 1,
        width: 1,
        content: "!",
    },
    {
        name: "Cross - ES - ES",
        input: [[[-1,0],"E"],[[0,-1],"S"]],
        output: [[[1,0],"E"],[[0,1],"S"]],
        height: 1,
        width: 1,
        content: "!",
    },
    {
        name: "Terminator - E",
        input: [[[-1,0],"E"]],
        output: [],
        height: 1,
        width: 1,
        content: `
o68$12b2o$12bo$10bobo$o2bo6b2o$4bo$o3bo$b4o!
`,
    },
];



// ************************************************************************* //
//  Symbolic computation
// ************************************************************************* //

type BExp =
    | { type: 'False' }
    | { type: 'True' }
    | { type: 'Var'; name : string; generation: number }
    | { type: 'Not'; op: BExp }
    | { type: 'And'; op1: BExp; op2: BExp }
    | { type: 'Or'; op1: BExp; op2: BExp }

const False : BExp = { type: 'False' };
const True : BExp = { type: 'True' };

type BExpEnv = { name : string; generation: number; value: boolean }[];
type BVar = { name : string; generation: number };
type BExp8 = { y1 : BExp, y2 : BExp, y3 : BExp, y4 : BExp,
               y5 : BExp, y6 : BExp, y7 : BExp, y8 : BExp };

function evalBExp(x: BExp, env: BExpEnv) : boolean {
    switch (x.type) {
        case 'False':
            return false;
        case 'True':
            return true;
        case 'Not':
            return !(evalBExp(x.op,env));
        case 'And':
            return (evalBExp(x.op1,env) && evalBExp(x.op2,env));
        case 'Or':
            return (evalBExp(x.op1,env) || evalBExp(x.op2,env));
        case 'Var':
            const v: string = x.name;
            const g: number = x.generation;
            let val = env.filter((elem) => elem.name == v && elem.generation == g);
            return val[0].value;
    }
}

function stringOfBExp(x: BExp, parent: string = "") : string {
    switch (x.type) {
        case 'False':
            return "false";
        case 'True':
            return "true";
        case 'Not':
            return "¬ " + stringOfBExp(x.op, x.type);
        case 'And':
            const s1 = stringOfBExp(x.op1,x.type);
            const s2 = stringOfBExp(x.op2,x.type);
            const and_res = s1 + " ∧ " + s2;
            if (parent == '' || parent == x.type) { return and_res; }
            return "(" + and_res + ")";
        case 'Or':
            const t1 = stringOfBExp(x.op1,x.type);
            const t2 = stringOfBExp(x.op2,x.type);
            const or_res = t1 + " ∨ " + t2;
            if (parent == '' || parent == x.type) { return or_res; }
            return "(" + or_res + ")";
        case 'Var':
            const v: string = x.name;
            const g: number = x.generation;
            return `${v}${g}`;
    }
}

function addToSortedArray(arr: BVar[], v: BVar): BVar[] {
    let insertIndex = arr.length;
    for (let i = 0; i < arr.length; i++) {
        if (arr[i].name === v.name &&
            arr[i].generation === v.generation) {
            return arr;
        }
        if (arr[i].name > v.name ||
            (arr[i].name === v.name &&
             arr[i].generation > v.generation)) {
            insertIndex = i;
            break;
        }
    }
    arr.splice(insertIndex, 0, v);
    return arr;
}

function getBVars(x: BExp, acc: BVar[]) : BVar[] {
    switch (x.type) {
        case 'False':
            return acc;
        case 'True':
            return acc;
        case 'Not':
            return getBVars(x.op,acc);
        case 'And':
            return getBVars(x.op1,getBVars(x.op2,acc));
        case 'Or':
            return getBVars(x.op1,getBVars(x.op2,acc));
        case 'Var':
            return addToSortedArray(acc, { name : x.name, generation : x.generation });
    }
}

function isTrue(x: BExp) : boolean { return (x.type === 'True'); }
function isFalse(x: BExp) : boolean { return (x.type === 'False'); }
function isVarA(x: BExp) : boolean { return (x.type === 'Var') && x.name === 'a'; }
function isVarB(x: BExp) : boolean { return (x.type === 'Var') && x.name === 'b'; }
function buildVar(n: string, g: number) : BExp {
    return { type : 'Var', name : n, generation : g };
}
function buildAnd(x: BExp, y: BExp) : BExp {
    return { type : 'And', op1 : x, op2 : y };
}
function buildOr(x: BExp, y: BExp) : BExp {
    return { type : 'Or', op1 : x, op2 : y };
}
function buildNot(x: BExp) : BExp {
    if (isFalse(x)) { return True; }
    if (isTrue(x)) { return False; }
    if (x.type === 'Not') {
        return x.op;
    } else {
        return { type : 'Not', op : x };
    }
}

function equalBExp(x : BExp, y: BExp) : boolean {
    switch (x.type) {
        case 'False':
            return isFalse(y);
        case 'True':
            return isTrue(y);
        case 'Not':
            if (y.type == 'Not') {
                return equalBExp(x.op,y.op);
            } else {
                return false;
            }
        case 'And':
            if (y.type == 'And') {
                return equalBExp(x.op1,y.op1) && equalBExp(x.op2,y.op2);
            } else {
                return false;
            }
        case 'Or':
            if (y.type == 'Or') {
                return equalBExp(x.op1,y.op1) && equalBExp(x.op2,y.op2);
            } else {
                return false;
            }
        case 'Var':
            if (y.type == 'Var') {
                return x.name == y.name && x.generation == y.generation;
            } else {
                return false;
            }
    }
}

function buildIfThenElse(x: BExp, y: BExp, z: BExp) : BExp {
    if (equalBExp(y,z)) { return y; }
    if (isTrue(y) && isFalse(z)) { return x; }
    if (isFalse(y) && isTrue(z)) { return buildNot(x); }
    if (isFalse(z)) { return buildAnd(x,y); }
    if (isTrue(y)) { return buildOr(x,z); }
    if (isTrue(z)) { return buildOr(y,buildNot(x)); }
    if (isFalse(y)) { return buildAnd(z,buildNot(x)); }
    return buildOr(buildAnd(x,y),buildAnd(buildNot(x),z));
}

function getBVars8(ys: BExp8) {
    return getBVars(ys.y1,getBVars(ys.y2,getBVars(ys.y3,getBVars(ys.y4,
        getBVars(ys.y5,getBVars(ys.y6,getBVars(ys.y7,getBVars(ys.y8,[]))))))));
}

function evalBExp8(ys: BExp8, env: BExpEnv) : number {
    let count : number = 0;
    if (evalBExp(ys.y1, env)) { count++; };
    if (evalBExp(ys.y2, env)) { count++; };
    if (evalBExp(ys.y3, env)) { count++; };
    if (evalBExp(ys.y4, env)) { count++; };
    if (evalBExp(ys.y5, env)) { count++; };
    if (evalBExp(ys.y6, env)) { count++; };
    if (evalBExp(ys.y7, env)) { count++; };
    if (evalBExp(ys.y8, env)) { count++; };
    return count;
}

function golEval(vars : BVar[], env: BExpEnv, x: BExp, ys: BExp8) : BExp {
    if (vars.length === 0) {
        const neighbors : number = evalBExp8(ys, env);
        const mid : boolean = evalBExp(x, env);
        let res : boolean = false;
        if (mid) {
            if (neighbors === 2 || neighbors === 3) { res = true; }
        } else {
            if (neighbors === 3) { res = true; }
        }
        return res ? True : False;
    } else {
        const newVars = vars.slice(1);
        const v = vars[0];
        const w : BExp = { type: 'Var', name : v.name, generation: v.generation } ;
        const envT = env.concat({ name : v.name, generation: v.generation, value : true });
        const envF = env.concat({ name : v.name, generation: v.generation, value : false });
        return buildIfThenElse(w,golEval(newVars,envT,x,ys),golEval(newVars,envF,x,ys));
    }
}

function countFalses(x: BExp, ys: BExp8) : number {
    let count : number = 0;
    if (isFalse(x)) { count++; };
    if (isFalse(ys.y1)) { count++; };
    if (isFalse(ys.y2)) { count++; };
    if (isFalse(ys.y3)) { count++; };
    if (isFalse(ys.y4)) { count++; };
    if (isFalse(ys.y5)) { count++; };
    if (isFalse(ys.y6)) { count++; };
    if (isFalse(ys.y7)) { count++; };
    if (isFalse(ys.y8)) { count++; };
    return count;
}

function golCell(x: BExp, ys: BExp8) : BExp {
    if (countFalses(x,ys) >= 7) { return False; }
    let vars : BVar[] = getBVars(x,getBVars8(ys));
    return golEval(vars,[],x,ys);
}

//console.log(golCell(True,{y1 : buildVar("b",2), y2 : buildVar("a",4), y3 : False, y4 : False,
//                           y5 : False, y6 : False, y7 : False, y8 : False}));

// ************************************************************************* //
//  Rest
// ************************************************************************* //

// Create the dropdown menu
const dropdown = document.createElement('select');
circuits.forEach((optionText) => {
    const option = document.createElement('option');
    option.value = optionText.name;
    option.textContent = optionText.name;
    dropdown.appendChild(option);
});
document.body.appendChild(dropdown);

const step_button = document.createElement('button');
step_button.textContent = 'step';
step_button.id = 'step_button';
document.body.appendChild(step_button);

const step60_button = document.createElement('button');
step60_button.textContent = 'step 60';
step60_button.id = 'step60_button';
document.body.appendChild(step60_button);

const run_button = document.createElement('button');
run_button.textContent = 'run';
run_button.id = 'run_button';
document.body.appendChild(run_button);

const stop_button = document.createElement('button');
stop_button.textContent = 'stop';
stop_button.id = 'stop_button';
document.body.appendChild(stop_button);

const rotate_button = document.createElement('button');
rotate_button.textContent = 'rotate';
rotate_button.id = 'rotate_button';
document.body.appendChild(rotate_button);

// New line
document.body.appendChild(document.createElement('br'));

// Set up the canvas
const canvas = document.createElement('canvas');
canvas.width = 320 * 5; // Grid size in pixels
canvas.height = 320 * 5;
document.body.appendChild(canvas);

const ctx = canvas.getContext('2d');
if (!ctx) {
    throw new Error('Failed to get the canvas rendering context');
}

// Parameters for the grid
let blockHeight: number = 1;
let blockWidth: number = 1;
let rows: number = 320; // Number of rows
let cols: number = 320; // Number of columns
let cellSize: number = canvas.width / cols; // Size of each cell
const updateInterval = 25; // Update interval in milliseconds
const black = '#000000';

// Create two grids (current and next state)
let grid: BExp[][] = [];
let nextGrid: BExp[][] = [];
let background: string[][] = [];
let inputs: CoordinateDirectionPair[] = [];
let outputs: CoordinateDirectionPair[] = [];
let stepCount: number = 0;
let genCount: number = 0;
let allowRun: boolean = false;
let lastLoadedCircut = circuits[0];
let latestClick : {x:number, y:number} = { x: -500, y: -500 };

// Function to initialize the grid from an RLE string
function initializeFromRLE(rle: string, startRow: number = 0, startCol: number = 0, fill : BExp = True) {
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
                        grid[row][col] = fill;
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

function drawTextBox(x: number, y: number, text: string) {
    if (!ctx) { return; }
    const padding = 10;
    const arrowHeight = 20;
    ctx.font = '16px Arial';
    const textMetrics = ctx.measureText(text);
    const textWidth = textMetrics.width;
    const textHeight = 16; // Approximate line height
    const bubbleWidth = textWidth + 2 * padding;
    const bubbleHeight = textHeight + 2 * padding;
    const bubbleX = x - bubbleWidth / 2;
    const bubbleY = y - bubbleHeight - arrowHeight;
    ctx.beginPath();
    ctx.rect(bubbleX, bubbleY, bubbleWidth, bubbleHeight);
    ctx.moveTo(x - 10, bubbleY + bubbleHeight);
    ctx.lineTo(x, y);
    ctx.lineTo(x + 10, bubbleY + bubbleHeight);
    ctx.closePath();
    ctx.fillStyle = 'yellow';
    ctx.fill();
    ctx.strokeStyle = 'yellow';
    ctx.stroke();
    ctx.fillStyle = 'black';
    ctx.fillText(text, bubbleX + padding, bubbleY + padding + textHeight * 0.85);
}

// Draw the grid on the canvas
function drawGrid() {
    if (!ctx) { return; }
    ctx.clearRect(0, 0, canvas.width, canvas.height); // Clear the canvas
    for (let row = 0; row < rows; row++) {
        for (let col = 0; col < cols; col++) {
            const cell : BExp = grid[row][col];
            if (isTrue(cell)) {
                ctx.fillStyle = '#FFFFFF';
            } else if (isFalse(cell)) {
                ctx.fillStyle = background[row][col];
            } else if (isVarA(cell)) {
                ctx.fillStyle = '#FF0000';
            } else if (isVarB(cell)) {
                ctx.fillStyle = '#00FF00';
            } else {
                ctx.fillStyle = '#BF40BF';
            }
            ctx.fillRect(col * cellSize, row * cellSize, cellSize, cellSize);
        }
    }
    if (latestClick.x > -200) {
        const x : number = Math.floor(latestClick.x / cellSize);
        const y : number = Math.floor(latestClick.y / cellSize);
        //const text = `x: ${x}, y: ${y}`;
        const text = stringOfBExp(grid[y][x]);
        drawTextBox(latestClick.x, latestClick.y, text);
    }
}

function toX(x:number) :number { return x+75+10; }
function toY(y:number) :number { return y+75+10; }

function deleteBox(x:number, y:number, w:number, h:number) {
    for (let i = 0; i < w; i++) {
        for (let j = 0; j < h; j++) {
            grid[toY(y+j)][toX(x+i)] = False;
        }
    }
}

function getCell(row : number, col : number) : BExp {
    if (0 <= row && row < rows && 0 <= col && col < cols) {
        return grid[row][col];
    } else {
        return False;
    }
}

const varNames : string[] = ["a","b","c","d"];

// Compute the next state of the grid
function computeNextState(ignoreInput: boolean = false) {
    for (let row = 0; row < rows; row++) {
        for (let col = 0; col < cols; col++) {
            const ns : BExp8 = {
                y1 : getCell(row-1,col+1),
                y2 : getCell(row-1,col),
                y3 : getCell(row-1,col-1),
                y4 : getCell(row,col+1),
                y5 : getCell(row,col-1),
                y6 : getCell(row+1,col+1),
                y7 : getCell(row+1,col),
                y8 : getCell(row+1,col-1),
            };
            nextGrid[row][col] = golCell(getCell(row,col), ns);
        }
    }
    // Swap grids (nextGrid becomes the current grid)
    [grid, nextGrid] = [nextGrid, grid];

    if (stepCount == 59) {
        outputs.forEach((output) => {
            if (output[1] == "E" || output[1] == "W") {
                const x = output[0][0];
                const y = output[0][1];
                deleteBox(75*x-6, 75*y-6, 12, 12);
            }
        });
        if (!ignoreInput) {
            inputs.forEach((input,index) => {
                if (input[1] == "E") {
                    const x = input[0][0];
                    const y = input[0][1];
                    const v : BExp = buildVar(varNames[index], genCount);
                    initializeFromRLE("$5bo2bo$9bo$5bo3bo$6b4o!",toY(75*y-5),toX(75*x-5),v);
                }
                if (input[1] == "W") {
                    const x = input[0][0];
                    const y = input[0][1];
                    const v : BExp = buildVar(varNames[index], genCount);
                    initializeFromRLE("5$4o$o3bo$o$bo2bo!",toY(75*y-5),toX(75*x-5),v);
                }
            });
        }
    }
    if (stepCount == 29) {
        outputs.forEach((output) => {
            if (output[1] == "N" || output[1] == "S") {
                const x = output[0][0];
                const y = output[0][1];
                deleteBox(75*x-6, 75*y-6, 12, 12);
            }
        });
        if (!ignoreInput) {
            inputs.forEach((input,index) => {
                if (input[1] == "N") {
                    const x = input[0][0];
                    const y = input[0][1];
                    const v : BExp = buildVar(varNames[index], genCount);
                    initializeFromRLE("2b3o$bo2bo$4bo$4bo$bobo!",toY(75*y-5),toX(75*x-5),v);
                }
                if (input[1] == "S") {
                    const x = input[0][0];
                    const y = input[0][1];
                    const v : BExp = buildVar(varNames[index], genCount);
                    initializeFromRLE("5$6bobo$5bo$5bo$5bo2bo$5b3o!",toY(75*y-5),toX(75*x-5),v);
                }
            });
        }
    }
    stepCount = (stepCount+1) % 60;
    if (stepCount === 0) { genCount++; }

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
    colourBox(-75,-75,150 * blockWidth,150 * blockHeight,'#000000');
    const port : string = '#111111';
    outputs.forEach((output) => {
        const x = output[0][0];
        const y = output[0][1];
        colourBox(75*x-6, 75*y-6, 12, 12, port);
    });
    inputs.forEach((input) => {
        const x = input[0][0];
        const y = input[0][1];
        colourBox(75*x-6, 75*y-6, 12, 12, port);

    });
}

function resizeGrid(width: number, height: number) {
    blockWidth = width;
    blockHeight = height;
    rows = height * 150 + 20;
    cols = width * 150 + 20;
    canvas.width = cols * 5;
    canvas.height = rows * 5;
    cellSize = canvas.width / cols;
    grid = [];
    nextGrid = [];
    background = [];
    stepCount = 0;
    genCount = 0;
    for (let row = 0; row < rows; row++) {
        grid[row] = [];
        nextGrid[row] = [];
        background[row] = [];
        for (let col = 0; col < cols; col++) {
            grid[row][col] = False;
            nextGrid[row][col] = False;
            background[row][col] = '#111111';
        }
    }
}

function loadCircuit(circuit) {
    lastLoadedCircut = circuit;
    const rleContent = circuit.content;
    inputs = circuit.input;
    outputs = circuit.output;
    resizeGrid(circuit.width, circuit.height);
    updateBackground();
    initializeFromRLE(rleContent, 10, 10);
    drawGrid();
}

// Function to handle dropdown changes
function handleDropdownChange(event: Event) {
    const selectedValue = (event.target as HTMLSelectElement).value;
    circuits.forEach((circuit) => {
        if (circuit.name == selectedValue) {
            loadCircuit(circuit);
        }
    });
}

loadCircuit(circuits[0]);

dropdown.addEventListener('change', handleDropdownChange);
step_button.addEventListener('click', () => {
    computeNextState();
    drawGrid();
});
step60_button.addEventListener('click', () => {
    for (let k = 0; k < 60; k++) {
        computeNextState();
    }
    drawGrid();
});
run_button.addEventListener('click', () => {
    allowRun = true;
    latestClick = { x: -500, y: -500 };
    requestAnimationFrame(gameLoop);
});
stop_button.addEventListener('click', () => {
    allowRun = false;
});
function rotateDir(dir: string) : string {
    if (dir == "E") { return "S" }
    if (dir == "S") { return "W" }
    if (dir == "W") { return "N" }
    return "E";
}
rotate_button.addEventListener('click', () => {
    if (stepCount > 0) {
        loadCircuit(lastLoadedCircut);
    }
    let tempGrid: BExp[][] = [];
    for (let i = 0; i < cols; i++) {
        tempGrid[i] = [];
        for (let j = 0; j < rows; j++) {
            tempGrid[i][j] = grid[(rows-1)-j][i];
        }
    }
    inputs = inputs.map((elem) =>
                [[2*(blockHeight-1)-elem[0][1],elem[0][0]],rotateDir(elem[1])]);
    outputs = outputs.map((elem) =>
                [[2*(blockHeight-1)-elem[0][1],elem[0][0]],rotateDir(elem[1])]);
    resizeGrid(blockHeight, blockWidth);
    updateBackground();
    grid = tempGrid;
    for (let k = 0; k < 30; k++) {
        computeNextState(true);
    }
    outputs.forEach((output) => {
        const x = output[0][0];
        const y = output[0][1];
        deleteBox(75*x-6, 75*y-6, 12, 12);
    });
    stepCount = 0;
    genCount = 0;
    allowRun = false;
    drawGrid();
});

canvas.addEventListener('mousemove', (event) => {
    const rect = canvas.getBoundingClientRect();
    latestClick = {
        x: event.clientX - rect.left,
        y: event.clientY - rect.top,
    };
    drawGrid();
});

canvas.addEventListener('click', (event) => {
    const rect = canvas.getBoundingClientRect();
    latestClick = {
        x: event.clientX - rect.left,
        y: event.clientY - rect.top,
    };
    drawGrid();
});

canvas.addEventListener('mouseleave', (event) => {
    latestClick = { x : -500, y : -500 };
    drawGrid();
});
