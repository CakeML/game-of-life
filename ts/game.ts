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
x = 634, y = 269, rule = B3/S23
o5$89bo49bo49bo49bo49bo49bo49bo49bo49bo49bo$89b3o9bo37b3o47b3o47b3o9bo
37b3o47b3o47b3o9bo37b3o47b3o47b3o9bo$92bo8bo40bo7b3o39bo7b2o40bo8bo40b
o7b3o39bo7b2o40bo8bo40bo7b3o39bo7b2o40bo8bo$91b2o7bob2obo35b2o11bo36b
2o8b2obo36b2o7bob2obo35b2o11bo36b2o8b2obo36b2o7bob2obo35b2o11bo36b2o8b
2obo36b2o7bob2obo$105bo45bo2bobo44b6o48bo45bo2bobo44b6o48bo45bo2bobo
44b6o48bo$94b2o6bo3bo39bo50bo8bo37b2o6bo3bo39bo50bo8bo37b2o6bo3bo39bo
50bo8bo37b2o6bo3bo$94bobo5bo2b2o38bobo4b4obo39bo3b3ob3o36bobo5bo2b2o
38bobo4b4obo39bo3b3ob3o36bobo5bo2b2o38bobo4b4obo39bo3b3ob3o36bobo5bo2b
2o$93bo2bo5bo4bo37bo2bo4b3o2bo39bo4bo3bo35bo2bo5bo4bo37bo2bo4b3o2bo39b
o4bo3bo35bo2bo5bo4bo37bo2bo4b3o2bo39bo4bo3bo35bo2bo5bo4bo$94b2o8bob2o
38b2o8bo39bo9b2o36b2o8bob2o38b2o8bo39bo9b2o36b2o8bob2o38b2o8bo39bo9b2o
36b2o8bob2o$94bo61bo2bo36b2o9b2o35bo61bo2bo36b2o9b2o35bo61bo2bo36b2o9b
2o35bo$108b2o49bo48b2o48b2o49bo48b2o48b2o49bo48b2o48b2o$99bo8bo49bo49b
o40bo8bo49bo49bo40bo8bo49bo49bo40bo8bo$97bobo9b3o47b3o47b3o35bobo9b3o
47b3o47b3o35bobo9b3o47b3o47b3o35bobo9b3o$98b2o11bo49bo49bo36b2o11bo49b
o49bo36b2o11bo49bo49bo36b2o11bo$140b2o148b2o148b2o$117b2o22b2o24b2o48b
2o48b2o22b2o24b2o48b2o48b2o22b2o24b2o48b2o48b2o$117bo22bo13bo12bo49bo
49bo22bo13bo12bo49bo49bo22bo13bo12bo49bo49bo$115bobo34bobo10bobo47bobo
47bobo34bobo10bobo47bobo47bobo34bobo10bobo47bobo47bobo$115b2o36b2o10b
2o48b2o48b2o36b2o10b2o48b2o48b2o36b2o10b2o48b2o48b2o$85b2o23b3o122b2o
23b3o122b2o23b3o122b2o23b3o$86b2o21b2ob2o122b2o21b2ob2o122b2o21b2ob2o
122b2o21b2ob2o$85bo23b2o2bo47b2o72bo23b2o2bo47b2o72bo23b2o2bo47b2o72bo
23b2o2bo$111b2o47bo2bo45b2o50b2o47bo2bo45b2o50b2o47bo2bo45b2o50b2o$
160bobo46bob2o97bobo46bob2o97bobo46bob2o$105bobo53bo18b2o30bo42bobo53b
o18b2o30bo42bobo53bo18b2o30bo42bobo$105b2o74b2o72b2o74b2o72b2o74b2o72b
2o$106bo9bo48bo14bo35bo39bo9bo48bo14bo35bo39bo9bo48bo14bo35bo39bo9bo$
112bob3o49b2o46bobo45bob3o49b2o46bobo45bob3o49b2o46bobo45bob3o$112bob
2o45b3obo46bo3bo45bob2o45b3obo46bo3bo45bob2o45b3obo46bo3bo45bob2o$111b
2obo10b2o23bobo12bo45b2o48b2obo10b2o23bobo12bo45b2o48b2obo10b2o23bobo
12bo45b2o48b2obo$114b2o10b2o22b2o8bo50b2ob2o48b2o10b2o22b2o8bo50b2ob2o
48b2o10b2o22b2o8bo50b2ob2o48b2o$112bobo10bo25bo10bob2o45b2o49bobo10bo
25bo10bob2o45b2o49bobo10bo25bo10bob2o45b2o49bobo$110bob3o45bob2o45b2o
3bo45bob3o45bob2o45b2o3bo45bob3o45bob2o45b2o3bo45bob3o$109b4o47b2o50bo
46b4o47b2o50bo46b4o47b2o50bo46b4o$70b2o35b3o47b2o36bobo9bo3bo8b2o35b3o
47b2o36bobo9bo3bo8b2o35b3o47b2o36bobo9bo3bo8b2o35b3o$71b2o33bobo47bobo
36b2o9bob2o11b2o33bobo47bobo36b2o9bob2o11b2o33bobo47bobo36b2o9bob2o11b
2o33bobo$70bo35bo49bo39bo9bo13bo35bo49bo39bo9bo13bo35bo49bo39bo9bo13bo
35bo$105b2o48b2o48b2o48b2o48b2o48b2o48b2o48b2o48b2o48b2o2$90bobo72b2o
73bobo72b2o73bobo72b2o73bobo$90b2o74b2o72b2o74b2o72b2o74b2o72b2o$91bo
73bo75bo73bo75bo73bo75bo3$110b2o23bobo122b2o23bobo122b2o23bobo$111b2o
22b2o124b2o22b2o124b2o22b2o$110bo25bo123bo25bo123bo25bo$573b2o$572bobo
$55b2o123bobo22b2o123bobo22b2o123bobo22b2o64b3o12bo$56b2o122b2o24b2o
122b2o24b2o122b2o24b2o49bobo10b3o8b2o3b4o$55bo125bo23bo125bo23bo125bo
23bo51bo2bo10b3o8b2o3b4o$542bo6bo10b2o10bobo2b2obob2o3bo2bo5b2o$517bo
23bobo5bo8bo3b2o9b2o2b2obobo4b4o5b2o$75bobo72b2o73bobo72b2o73bobo72b2o
65b3o5bobo12bob2o6bo9b2o17b2obo3b4o$25bo2b2o45b2o74b2o72b2o74b2o72b2o
74b2o67bo4b2o7b2o3b2ob2o9b2o2bo2bo25bo$23b3o2b2o46bo73bo75bo73bo75bo
73bo68b2o5bo7b2o4bob2o5b3o2bo2bobo$22bo518bobo7b4o$22b2o497b3o18bo9b2o
18bo6b2o9b2o$9b2o84b2o23bobo122b2o23bobo122b2o23bobo98b3o46b2o6bo2bo7b
o2bo$10bo85b2o22b2o124b2o22b2o124b2o22b2o149b2o5b3o9b3o$10bobo82bo25bo
123bo25bo123bo25bo159b9o$11b2o4b2o541bo19bo2b5o2bo$16bo2bo499b2o3b2o
35b2o17b2o2b3o2b2o$16bo2bo20b2o123bobo22b2o123bobo22b2o123bobo22b2o28b
5o35b2o$16bo2bo21b2o122b2o24b2o122b2o24b2o122b2o24b2o28b3o$o2bo11bo2bo
9bo11bo125bo23bo125bo23bo125bo23bo31bo47bo2bo$4bo9bo2bo11bo544bo$o3bo
12bo9b3o540bo3bo$b4o9bo2bo30bo11bobo72b2o73bobo72b2o73bobo72b2o134b4o$
15b3o4b2o22b3o11b2o74b2o72b2o74b2o72b2o74b2o$22bo22bo15bo73bo75bo73bo
75bo73bo119bo8b2o$23b3o19b2o472b2o32bobo6bo2bo$25bo494bo25b2o4bobo7bo
3bo2b2o$18b2obo11b2o6bob2o35b2o23bobo122b2o23bobo122b2o23bobo109b3o26b
2o3bo2bo7bo2b2o2b3o$9b2o3b2o2b2ob3o8bo2bo3bo4bo36b2o22b2o124b2o22b2o
124b2o22b2o110bo34bobo16b2obo5b2o$9bo2bo2bo8bo7bobo4bo2b2o36bo25bo123b
o25bo123bo25bo146bobo4b3o8bo2bo5b2o$10b5o3b2ob3o9bo5bo3bo511bo15b2obo$
19bobo20bo526b3o$12b2obo3bobo6b2o7bob2obo107bobo22b2o123bobo22b2o123bo
bo22b2o92b2o13b2o$12bob2o4bo8bo8bo111b2o24b2o122b2o24b2o122b2o24b2o
105bobo$26b3o9bo112bo23bo125bo23bo125bo23bo109bo$26bo2$45bobo72b2o73bo
bo72b2o73bobo72b2o$45b2o74b2o72b2o74b2o72b2o74b2o$46bo73bo75bo73bo75bo
73bo$551bo$552bo$65b2o23bobo122b2o23bobo122b2o23bobo157b3o$66b2o22b2o
124b2o22b2o124b2o22b2o$65bo25bo123bo25bo123bo25bo3$135bobo22b2o123bobo
22b2o123bobo22b2o$135b2o24b2o122b2o24b2o122b2o24b2o$136bo23bo125bo23bo
125bo23bo$581b2o$581b2o$30bobo72b2o73bobo72b2o73bobo72b2o$30b2o74b2o
72b2o74b2o72b2o74b2o$31bo73bo75bo73bo75bo73bo175bo$561b3o5bo10b3o$11b
2o48b2o48b2o48b2o48b2o48b2o48b2o48b2o48b2o150bo4b2o9bo3bo$12bo37b2o10b
o12bobo34bo49bo37b2o10bo12bobo34bo49bo37b2o10bo12bobo34bo149bo5bobo10b
o$12bobo36b2o9bobo10b2o35bobo47bobo36b2o9bobo10b2o35bobo47bobo36b2o9bo
bo10b2o35bobo163bo5bo$13b2o35bo12b2o11bo36b2o48b2o35bo12b2o11bo36b2o
48b2o35bo12b2o11bo36b2o163bo5bo$18bo149bo149bo226bobo31bo3bo$16b2ob2o
145b2ob2o145b2ob2o222bo3bo5b3o24b3o$16bo2bo47b2o76b2o19bo2bo47b2o76b2o
19bo2bo47b2o76b2o96bo7bobo2bo2b2o$17b2o47bo2bo49b2o25b2o19b2o47bo2bo
49b2o25b2o19b2o47bo2bo49b2o25b2o88b2o4bo4bo7b2o2bo2bo13b2o$23bo43bobo
46b2o2bo24bo27bo43bobo46b2o2bo24bo27bo43bobo46b2o2bo24bo90b2o5bo19bo
11b2o$24bo43bo49bo55bo43bo49bo55bo43bo49bo124bo3bo2b3o10bo6b2o5bo$22b
3o147b3o147b3o220bobo15bo6b2o$14bo48bo26b2o21bo50bo48bo26b2o21bo50bo
48bo26b2o21bo145bo2bo$12b2o49bobo25b2o20b3obo44b2o49bobo25b2o20b3obo
44b2o49bobo25b2o20b3obo141b2o$14bob3o44bo3bo10bo11bo23b2obo46bob3o44bo
3bo10bo11bo23b2obo46bob3o44bo3bo10bo11bo23b2obo$14bo52b2o10bo35bob2o
45bo52b2o10bo35bob2o45bo52b2o10bo35bob2o$19bo44b2ob2o8b3o34b2o53bo44b
2ob2o8b3o34b2o53bo44b2ob2o8b3o34b2o163bo$14b2obo17b2o11bo18b2o29bo16bo
bo30bo15b2obo17b2o11bo18b2o29bo16bobo30bo15b2obo17b2o11bo18b2o29bo16bo
bo30bo129b3o$16b2obo16b2o8b3o16bo3b2o25b3o16b3obo26b3o17b2obo16b2o8b3o
16bo3b2o25b3o16b3obo26b3o17b2obo16b2o8b3o16bo3b2o25b3o16b3obo26b3o129b
3o$18b2o15bo9bo21bo27bo21b4o24bo22b2o15bo9bo21bo27bo21b4o24bo22b2o15bo
9bo21bo27bo21b4o24bo$21b2o22b2o21bo3bo22b2o23b3o23bo24b2o22b2o21bo3bo
22b2o23b3o23bo24b2o22b2o21bo3bo22b2o23b3o23bo129b2o3b2o$21bobo7b2o11b
2o24b2obo47bobo9b2o8bo2bo24bobo7b2o11b2o24b2obo47bobo9b2o8bo2bo24bobo
7b2o11b2o24b2obo47bobo9b2o8bo2bo129b2o3b2o$23bo6b3o10b2o28bo9b2o6bob2o
28bo9bo9bo29bo6b3o10b2o28bo9b2o6bob2o28bo9bo9bo29bo6b3o10b2o28bo9b2o6b
ob2o28bo9bo9bo$23b2o5bo2bo6bo3bo28b2o7bo2bo3bo4bo28b2o9bo5b3o2bo27b2o
5bo2bo6bo3bo28b2o7bo2bo3bo4bo28b2o9bo5b3o2bo27b2o5bo2bo6bo3bo28b2o7bo
2bo3bo4bo28b2o9bo5b3o2bo$30b2obo4b3ob3o37bobo4bo2b2o40b2o3b4obo35b2obo
4b3ob3o37bobo4bo2b2o40b2o3b4obo35b2obo4b3ob3o37bobo4bo2b2o40b2o3b4obo
134bo$31b2o10bo39bo5bo3bo87b2o10bo39bo5bo3bo87b2o10bo39bo5bo3bo184bobo
$38b6o48bo45bo2bobo44b6o48bo45bo2bobo44b6o48bo45bo2bobo133b2o$28b2o8b
2obo36b2o7bob2obo35b2o11bo36b2o8b2obo36b2o7bob2obo35b2o11bo36b2o8b2obo
36b2o7bob2obo35b2o11bo135b2o$29bo7b2o40bo8bo40bo7b3o39bo7b2o40bo8bo40b
o7b3o39bo7b2o40bo8bo40bo7b3o137b3o$26b3o47b3o9bo37b3o47b3o47b3o9bo37b
3o47b3o47b3o9bo37b3o149bobo$26bo49bo49bo49bo49bo49bo49bo49bo49bo152b2o!
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

const step_button = document.createElement('button');
step_button.textContent = 'step';
step_button.id = 'step_button';
document.body.appendChild(step_button);

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
let grid: number[][] = [];
let nextGrid: number[][] = [];
let background: string[][] = [];
let inputs: CoordinateDirectionPair[] = [];
let outputs: CoordinateDirectionPair[] = [];
let stepCount: number = 0;
let allowRun: boolean = false;
let lastLoadedCircut = circuits[0];

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
function computeNextState(ignoreInput: boolean = false) {
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
        if (!ignoreInput) {
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
    }
    if (stepCount == 29) {
        outputs.forEach((output) => {
            if (output[1] == "N" || output[1] == "S") {
                const x = output[0][0];
                const y = output[0][1];
                deleteBox(75*x-5, 75*y-5, 10, 10);
            }
        });
        if (!ignoreInput) {
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
    colourBox(-75,-75,150 * blockWidth,150 * blockHeight,'#301934');
    outputs.forEach((output) => {
        const x = output[0][0];
        const y = output[0][1];
        if (x % 2 === 0) {
            colourBox(75*x-5, 75*y-6, 10, 12, '#483248');
        } else {
            colourBox(75*x-6, 75*y-5, 12, 10, '#483248');
        }
    });
    inputs.forEach((input) => {
        const x = input[0][0];
        const y = input[0][1];
        if (x % 2 === 0) {
            colourBox(75*x-5, 75*y-6, 10, 12, '#483248');
        } else {
            colourBox(75*x-6, 75*y-5, 12, 10, '#483248');
        }
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
    for (let row = 0; row < rows; row++) {
        grid[row] = [];
        nextGrid[row] = [];
        background[row] = [];
        for (let col = 0; col < cols; col++) {
            grid[row][col] = 0;
            nextGrid[row][col] = 0;
            background[row][col] = black;
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
run_button.addEventListener('click', () => {
    allowRun = true;
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
    let tempGrid: number[][] = [];
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
    stepCount = 0;
    allowRun = false;
    drawGrid();
});
