// ************************************************************************* //
//  Circuits
// ************************************************************************* //
var circuits = [
    {
        name: "Generate1_E",
        input: [],
        output: [[[3, 0], "E"]],
        height: 2,
        width: 2,
        drawing: "--ro-r--r--",
        content: "\no29bo2$29bo$29b4o$13bo16b4o$12bobo5b2o8bo2bo5b2o$10b2o3bo14b4o5b2o$5b\n2o3b2o3bo4bobob2o3b4o$5b2o3b2o3bo5b2o3bo2bo$12bobo10bo$13bo8bo2bo$30bo\n2bo$7b2o25bo$6bo2bo20bo3bo$6bo24b4o$6bo$6bobo11bo$6bobo11b2o$7bo11bobo\n17b2o7b2o$39bo9bo$30bo9b9o$4b2o3b2o18b2o6b3o2b5o2b3o$4bo5bo18bobo5bo2b\no2b3o2bo2bo$38b2o9b2o$5bo3bo2b2o$6b3o4b2o$12bo$49bo$36b2o2b2o6b4o$31bo\nbo2bob4o5b2obobo3b2o$o28bo3bo3bob2o5b3obo2bo2b2o$22b2o5bo12bo4b2obobo$\n9bo12b2o4bo4bo14b4o$7b2ob2o17bo19bo$29bo3bo$6bo5bo18bobo2$6b2obob2o9$\n9b2o$9b2o!\n",
    },
    {
        name: "Generate2_E",
        input: [],
        output: [[[3, 2], "E"]],
        height: 2,
        width: 2,
        drawing: "--r-or--r--",
        content: "\no29bo9$8b2o$8b2o11$5b2o3b2o18bo$7b3o18bobo$6bo3bo16bobo17bo$7bobo11b2o\n3bo2bo16b2o$8bo12b2o4bobo15b2o4b2o$28bobo13b3o4b2o2b2o$30bo4bobo7b2o4b\n2o2b2o$35b2o9b2o$36bo10bo$o4b3o$11bobo$5bobo4b2o$4b5o3bo24b2o9b2o$3b2o\n3b2o19bo6bo2bo7bo2bo$3b2o3b2o17b2o7b3o9b3o$28b2o9b9o$38bo2b5o2bo$6bo\n12bo18b2o2b3o2b2o$4b2o14b2o$19b2o$3bo26bo2bo$34bo$4bo2bo22bo3bo$6b2o\n23b4o2$12b2o$10bo3bo5bo2b3o$4b2o3bo5bo9bo3bo$4b2o2b2obo3bo8bo4bobo$9bo\n5bo16b2o4b2o$10bo3bo17b2o4b2o$12b2o18b2o$29bobo$29bo!\n",
    },
    {
        name: "Generate1_EX",
        input: [],
        output: [[[3, 0], "EX"]],
        height: 2,
        width: 2,
        drawing: "--ro-r--r--",
        content: "\no$28b2o$28bo2bo$14bobo15bo$12bo3bo2b3o10bo6b2o$12bo19bo6b2o$5b2o4bo4bo\n7b2o2bo2bo$5b2o5bo7bobo2bo2b2o$12bo3bo5b3o$14bobo$28bo2bo$7b2o23bo11b\n4o$7b2o19bo3bo10bo3bo$29b4o14bo$43bo2bo$7bo$6b3o10bo$5bo3bo9b2o18b2o2b\n3o2b2o$7bo10bobo18bo2b5o2bo$4bo5bo29b9o$4bo5bo20bo5b3o9b3o$5bo3bo20b2o\n5bo2bo7bo2bo$6b3o21bobo5b2o9b2o2$11b2o$12b2o$11bo27bo7bo$38b4o5bobo$\n33b2o2bo2b2o8b2o4b2o$33b2o2b2o11b2o4b2o$o21b2o6b2o10bo7b2o$22b2o5b3o\n10bo4bobo$9bo20b2o10bo4bo$8b3o22b2o$8b3o22b2o2$6b2o3b2o$6b2o3b2o3$9bo$\n8bobo$7b2o$7b2o$7b3o$8bobo$9b2o!\n",
    },
    {
        name: "Generate2_EX",
        input: [],
        output: [[[3, 2], "EX"]],
        height: 2,
        width: 2,
        drawing: "--r-or--r--",
        content: "\no8$8b2o$8b2o3$6bo$7bo$7bo3$5b2o3b2o$8bo$5bo5bo$6b2ob2o20bobo$7bobo20bo\n2bo$8bo20b2o10bo6bo$8bo12b2o4b2o3bo8bo5bobo$21b2o6b2o9bo6b2obo$30bo2bo\n2b2o9b2ob2o3b2o$31bobo2bo2b3o5b2obo4b2o$36b4o7bobo$37b2o9bo$10bobo$o\n10b2o$5b3o3bo$4bo3bo21bo6b2o9b2o$3bo5bo18b2o6bo2bo2b3o2bo2bo$3b2obob2o\n19b2o5b3o2b5o2b3o$39b9o$18bo19bo9bo$6bo12b2o17b2o7b2o$5bobo10b2o$5bobo\n$6bo21bo2bo$32bo11b4o$6b2o20bo3bo10bo3bo$6b2o21b4o14bo$43bo2bo$13bo8b\n2o$11bobo6bo2bo$4b2o4bobo7bo3bo2b2o$4b2o3bo2bo7bo2b2o2b3o$10bobo16b2ob\no5b2o$11bobo4b3o8bo2bo5b2o$13bo15b2obo$27b3o$27b2o!\n",
    },
    {
        name: "Generate2_EY",
        input: [],
        output: [[[3, 2], "EY"]],
        height: 2,
        width: 2,
        drawing: "--r-or--r--",
        content: "\no29bo8$7b2o$7b2o3$5bo$6bo$6bo3$4b2o3b2o$7bo$4bo5bo$5b2ob2o20bobo$6bobo\n20bo2bo$7bo20b2o10bo6bo$7bo12b2o4b2o3bo8bo5bobo$20b2o6b2o9bo6b2obo$29b\no2bo2b2o9b2ob2o3b2o$30bobo2bo2b3o5b2obo4b2o$35b4o7bobo$36b2o9bo$9bobo$\no9b2o$4b3o3bo$3bo3bo21bo6b2o9b2o$2bo5bo18b2o6bo2bo2b3o2bo2bo$2b2obob2o\n19b2o5b3o2b5o2b3o$38b9o$17bo19bo9bo$5bo12b2o17b2o7b2o$4bobo10b2o$4bobo\n$5bo21bo2bo$31bo11b4o$5b2o20bo3bo10bo3bo$5b2o21b4o14bo$42bo2bo$12bo8b\n2o$10bobo6bo2bo$3b2o4bobo7bo3bo2b2o$3b2o3bo2bo7bo2b2o2b3o$9bobo16b2obo\n5b2o$10bobo4b3o8bo2bo5b2o$12bo15b2obo$26b3o$26b2o!\n",
    },
    {
        name: "Collide_EXN_EXN",
        input: [[[-1, 0], "EX"], [[0, 1], "N"]],
        output: [[[1, 0], "EX"], [[0, -1], "N"]],
        height: 1,
        width: 1,
        drawing: "ororiri",
        content: "!",
    },
    {
        name: "Collide_EXS_EXS",
        input: [[[-1, 0], "EX"], [[0, -1], "S"]],
        output: [[[1, 0], "EX"], [[0, 1], "S"]],
        height: 1,
        width: 1,
        drawing: "irorori",
        content: "!",
    },
    {
        name: "Collide_stop_EXN_N",
        input: [[[-1, 0], "EX"], [[0, 1], "N"]],
        output: [[[0, -1], "N"]],
        height: 1,
        width: 1,
        drawing: "or-riri",
        content: "\no7$20b2o$20bo$18bobo$o2bo14b2o$4bo$o3bo$b4o10$12b3o$11bo2bo$14bo$14bo$\n11bobo!\n",
    },
    {
        name: "Collide_stop_EXN_EX",
        input: [[[-1, 0], "EX"], [[0, 1], "N"]],
        output: [[[1, 0], "EX"]],
        height: 1,
        width: 1,
        drawing: "-roriri",
        content: "\no4$8bo$8b3o$11bo$10b2o3$o2bo$4bo$o3bo$b4o10$12b3o$11bo2bo$14bo$14bo$\n11bobo!\n",
    },
    {
        name: "Collide_stop_EXS_EX",
        input: [[[-1, 0], "EX"], [[0, -1], "S"]],
        output: [[[1, 0], "EX"]],
        height: 1,
        width: 1,
        drawing: "iror-ri",
        content: "\no19$13b2o$14bo$11b3o$11bo!\n",
    },
    {
        name: "Not_turn_EX_S",
        input: [[[-1, 4], "EX"]],
        output: [[[2, 5], "S"]],
        height: 3,
        width: 3,
        drawing: "---r---r-o-ri--",
        content: "\no29bo2$58b2o$58b2o11$40b2o14b2o3b2o$40b2o16b3o$57bo3bo$58bobo$59bo5$\n60b3o$54bobo$37b2o3b2o10b2o4bobo$55bo3b5o$38bo3bo15b2o3b2o$39b3o16b2o\n3b2o$39b3o2$48bo$46b2o12b2o$47b2o2$38bo5bo6b2o$37b3o5bo4b2o$37b3o3b3o\n6bo2$35b2o3b2o19b2obob2o$35b2o3b2o19bo5bo$62bo3bo$59bo3b3o$38bo19b2o$\n37bobo18bobo$36b2o6bobo$36b2o9bo6b2o$36b3o8bo6bobo$37bobo4bo2bo3b2obob\no$38b2o5b3o3bobobo$53bo8bo$53b2o7bo$53b3o5bobo$53b3o4b2ob2o$53b3o3bo5b\no$53b2o7bo$53bo5b2o3b2o$51bobobo$51b2obobo$54bobo6bo$15bob2o4bo30b2o7b\no$15b2obo3bobo39bo$22bobo$13b5o3b2ob3o$12bo2bo2bo8bo33b2o$12b2o3b2o2b\n2ob3o34b2o$21b2obo$28bo$26b3o$25bo$25b2o$14b4o$13bo3bo$17bo$13bo2bo$\n22b2o20bobo$21bo2bo22bo$22b2o23bo$14b2o28bo2bo$13bobo29b3o$13bo$12b2o$\n25b2o$25bo$26b3o$28bo!\n",
    },
    {
        name: "Not_turn_EX_N",
        input: [[[-1, 0], "EX"]],
        output: [[[2, -1], "N"]],
        height: 2,
        width: 3,
        drawing: "-o-r--r---r-i",
        content: "\no29bo4$59b2o$59b2o$59b2o$60bo$59bobo$59bobo$42b3o6b2o7bo$14b4o24bo2bo\n5bobo$13bo3bo24bo5b2obobo$17bo24bo5bobobo4b2o3b2o$13bo2bo26bobo4bo6bob\nobobo$49b2o7b5o$48b3o8b3o$48b3o9bo$48b3o$49b2o$50bo$35b2o11bobobo$35b\n2o11b2obobo$51bobo$51b2o4bobo$42b3o12b2o$35bo5bo2bo13bo$34b3o7bo$33bo\n3bo6bo$32bob3obo2bobo17b3o$33b5o22bo3bo$51bo7bo5bo$49b2o9bo3bo$50b2o9b\n3o$61b3o$38b3o$40bo$39bo$61b2o$46b2o13b2o$45b2o$47bo3$36b3o$35bo3bo$\n34bo5bo13bo$34b2obob2o12b2o$53bobo$64bo$37bo25bobo$36bobo13bo8b2o3bo9b\n2o$36bobo13b4o5b2o3bo9b2o$37bo4b2o9b4o4b2o3bo$42b2o9bo2bo6bobo$37b2o8b\no5b4o7bo$37b2o8bo4b4o$52bo!\n",
    },
    {
        name: "Not_turn_N_EX",
        input: [[[2, 3], "N"]],
        output: [[[3, 2], "EX"]],
        height: 2,
        width: 2,
        drawing: "--r-ori-r--",
        content: "\no8$6b2o$6b2o11$3b2o3b2o18bo$5b3o18bobo$4bo3bo16bobo17bo$5bobo11b2o3bo\n2bo16b2o$6bo12b2o4bobo15b2o4b2o$26bobo13b3o4b2o2b2o$28bo4bobo7b2o4b2o\n2b2o$33b2o9b2o$34bo10bo$3b3o$o8bobo$3bobo4b2o$2b5o3bo24b2o9b2o$b2o3b2o\n19bo6bo2bo2b3o2bo2bo$b2o3b2o17b2o7b3o2b5o2b3o$26b2o9b9o$36bo9bo$4bo12b\no18b2o7b2o$2b2o14b2o$17b2o$bo26bo2bo$32bo11b4o$2bo2bo22bo3bo10bo3bo$4b\n2o23b4o14bo$43bo2bo$10b2o$8bo3bo5bo2b3o$2b2o3bo5bo9bo3bo$2b2o2b2obo3bo\n8bo4bobo$7bo5bo16b2o4b2o$8bo3bo17b2o4b2o$10b2o18b2o$27bobo$27bo!\n",
    },
    {
        name: "Not_turn_S_EX",
        input: [[[4, -1], "S"]],
        output: [[[5, 0], "EX"]],
        height: 2,
        width: 3,
        drawing: "",
        content: "\no29bo29bo$42bo$42bobo$25b2o18b2o$23bo3bo17b2o4b2o$22bo5bo16b2o4b2o$17b\n2o2b2obo3bo8bo4bobo$17b2o3bo5bo9bo3bo$23bo3bo5bo2b3o$25b2o2$44b4o26b4o\n$43bo3bo25bo3bo$47bo29bo$43bo2bo26bo2bo$32b2o$33b2o$32bo18b2o2b3o2b2o$\n51bo2b5o2bo$41b2o9b9o$40b2o7b3o9b3o$42bo6bo2bo7bo2bo$14bo10bo24b2o9b2o\n15b2o$14b2o9b2o51bo$5b2o2b2o4b2o7bobo4bo47b3o$5b2o2b2o4b3o13bobo15b2o\n9bo20bo$9b2o4b2o15bobo13b4o7bobo$14b2o16bo2bo7bobo2bo2b3o5b2obo4b2o$\n14bo17bobo7bo2bo2b2o9b2ob2o3b2o$31bobo7b2o9bo6b2obo$o30bo7b2o3bo8bo5bo\nbo$41b2o10bo6bo$42bo2bo$43bobo!\n",
    },
    {
        name: "Turn_E_N",
        input: [[[-1, 0], "E"]],
        output: [[[2, -1], "N"]],
        height: 3,
        width: 3,
        drawing: "-o-r---r---r--i",
        content: "\no29bo29bo29bo11$o2bo26bo2bo$4bo29bo$o3bo25bo3bo$b4o26b4o4$27b2o$27b2o\n4$34b2o29b2o16b2o$26b3o4bobo29bobo15b2o$26b3o4bobob2o21b2o3bo$25bo3bo\n4bobobo21b2o$36bo$24b2o3b2o4b2o$34b3o$34b3o24bo20b3o$34b3o23bobo$35b2o\n22bo3bo6b2o2b3o5bobo$24b3o9bo23b3o7bobobo6b5o$28b2o4bobobo11b2o6b2o3b\n2o6b2o7b2o3b2o$28b2o3bobob2o11b2o20bo7b2o3b2o$29b2o2bobo$27bobo4b2o$\n27b2o51b2o$64b2o12b2obo$42b3o20b2o11bo$22b2o3b2o13bo2bo4b3o11bo$22b2o\n3b2o13bo6b2ob2o25b3obo$34bo7bo6b2ob2o29bo$24b3o8b2o6bobo3b5o29bo$24b3o\n7b2o12b2o3b2o$25bo2$48bo14bo$46b2obo12b3o13b2o3b2o$49bo11b5o14b3o$60b\n2o3b2o12bo3bo$28bo17bob2o30bobo$26b2ob2o7b2o8bo2bo29bo$39b2o8bobo$25bo\n5bo6bo23b3o$62b3o$25b2obob2o49b2o$81b2o$48b3o11b2o$31b2o14bo3bo10b2o$\n30bobo13bo5bo$31bo15bo3bo$30b2o16b3o$30b3o15b3o$31b2o$29bo2$48b2o$48b\n2o$30bo$29b3o$28b5o$27b2o3b2o$28b5o$28bo3bo$29bobo$30bo3$30b2o$30b2o!\n",
    },
    {
        name: "Turn_E_S",
        input: [[[-1, 4], "E"]],
        output: [[[2, 5], "S"]],
        height: 3,
        width: 3,
        drawing: "---r---r-o-ri--",
        content: "\no29bo29bo3$48bo5b2o$40b2o4bo3bo3b3o$40b2o8bo5b2obo8bo$45bo5bo4bo2bo6bo\nbo$45b2o9b2obo5bobo$40bo13b3o7bo2bo11b2o$39b3o12b2o9bobo11b2o$38bo3bo\n23bobo$40bo17bo9bo$37bo5bo12b2o$37bo5bo13b2o$38bo3bo$39b3o4$49bobo$42b\no6b2o$50bo13b2o$64b2o$42bo$40bobo$41b2o$65bo$54bo9bobo$53b2o8bo3bo$35b\n2o3b2o11bobo8b3o$o29bo15bobo13b2o3b2o$36bo3bo4bo$37b3o5bo$37b3o5bo2bo$\n45b3o$61b2o$54b2o4b2o$54bobo5bo$38b2o11b2obobo$38b2o11bobobo$53bo$53b\n2o$27bo25b3o$25bobo25b3o$15b2o6b2o12b2o14b3o7bo$14bo3bo4b2o12b2o5bobo\n6b2o7b3o$3b2o8bo5bo3b2o22bo5bo7b5o$3b2o8bo3bob2o4bobo19bo3bobobo4b2o3b\n2o$13bo5bo7bo16bo2bo3b2obobo$14bo3bo26b3o6bobo$15b2o37b2o$26bo35b3o$\n27b2o33b3o$26b2o2$62b2o$62b2o3$33bobo$o33b2o$17bob2o4bo8bo$17b2obo3bob\no$24bobo$15b5o3b2ob3o$14bo2bo2bo8bo$14b2o3b2o2b2ob3o12bo$23b2obo15b2o$\n30bo10b2o$28b3o$27bo$o2bo23b2o$4bo$o3bo$b4o16bo26bobo$20b3o7b2o17b2o$\n19bo2bo6bobo17bo$19b3o9bo$20bo32b2o$16b2o35bobo$15bobo37bo$15bo39b2o$\n14b2o$27b2o$27bo$28b3o$30bo!\n",
    },
    {
        name: "Turn_Middle_E_S",
        input: [[[-1, 2], "E"]],
        output: [[[4, 5], "S"]],
        height: 3,
        width: 4,
        drawing: "----r---r-o--r-i-",
        content: "\no59bo29bo$9b2o19b2o$9b2o19b2o$78bo5b2o$70b2o4bo3bo3b3o$70b2o8bo5b2obo\n8bo$75bo5bo4bo2bo6bobo$75b2o9b2obo5bobo$70bo13b3o7bo2bo11b2o$9b3o57b3o\n12b2o9bobo11b2o$8bo3bo17bo37bo3bo23bobo$29b3o38bo17bo9bo$7bo5bo14b5o\n34bo5bo12b2o$7b2o3b2o13b2o3b2o33bo5bo13b2o$68bo3bo$69b3o$10bo$8b2obo\n17b3o$11bo17b3o$7bo3bo67bobo$7bo2bo21bo39bo6b2o$6b5o20bobo46bo13b2o$6b\n5o19bo3bo59b2o$5b2o3b2o12b2o5b3o38bo$6b5o12bo2bo2b2o3b2o34bobo$7b3o5bo\nbo4bo48b2o$8bo7b2o5bob2o68bo$16bo67bo9bobo$21bobo59b2o8bo3bo$21bobo41b\n2o3b2o11bobo8b3o$o75bobo13b2o3b2o$66bo3bo4bo$67b3o5bo$67b3o5bo2bo$75b\n3o$7b2o23b2o57b2o$7b2o23b2o50b2o4b2o$84bobo5bo$68b2o11b2obobo$68b2o11b\nobobo$30bobo50bo$o2bo27b2o50b2o$4bo26bo51b3o$o3bo78b3o$b4o78b3o7bo$74b\nobo6b2o7b3o$77bo5bo7b5o$77bo3bobobo4b2o3b2o$74bo2bo3b2obobo$75b3o6bobo\n$84b2o$92b3o$92b3o3$45bobo44b2o$46b2o44b2o$46bo$58b3o$60bo$o58bo9bo$\n67b3o$66bo$66b2o$65b2o$54b2o8b2o$53bo2bo4bo3bo$53bobo3b3ob3o$54bo9bo$\n59b6o$49b2o8b2obo$50bo7b2o$47b3o$47bo!\n",
    },
    {
        name: "Not_Turn_E_S",
        input: [[[-1, 4], "E"]],
        output: [[[2, 5], "S"]],
        height: 3,
        width: 3,
        drawing: "---r---r-o-ri--",
        content: "\no29bo29bo3$48bo5b2o$40b2o4bo3bo3b3o$40b2o8bo5b2obo8bo$45bo5bo4bo2bo6bo\nbo$45b2o9b2obo5bobo$40bo13b3o7bo2bo11b2o$39b3o12b2o9bobo11b2o$38bo3bo\n23bobo$40bo17bo9bo$37bo5bo12b2o$37bo5bo13b2o$38bo3bo$39b3o4$49bobo$42b\no6b2o$50bo13b2o$64b2o$42bo$40bobo$41b2o$65bo$54bo9bobo$53b2o8bo3bo$35b\n2o3b2o11bobo8b3o$o29bo15bobo13b2o3b2o$36bo3bo4bo$37b3o5bo$37b3o5bo2bo$\n45b3o$61b2o$54b2o4b2o$54bobo5bo$38b2o11b2obobo$38b2o11bobobo$53bo$53b\n2o$53b3o$53b3o$53b3o7bo$44bobo6b2o7b3o$47bo5bo7b5o$47bo3bobobo4b2o3b2o\n$44bo2bo3b2obobo$45b3o6bobo$54b2o$62b3o$62b3o3$62b2o$62b2o4$o$11bob2o\n4bo$11b2obo3bobo$18bobo$9b5o3b2ob3o$8bo2bo2bo8bo$8b2o3b2o2b2ob3o$17b2o\nbo$24bo$22b3o$14b3o4bo$o2bo10bo2bo3b2o$4bo9bo12b2o$o3bo9bo3bo7bobo$b4o\n13bo9bo2$13bo5bo$19bo$14bo4bo$10b2o4b2o$9bobo$9bo$8b2o$21b2o$21bo$22b\n3o$24bo!\n",
    },
    {
        name: "Not_Turn_E_N",
        input: [[[-1, 2], "E"]],
        output: [[[4, -1], "N"]],
        height: 4,
        width: 3,
        drawing: "--or----r---r--i-",
        content: "\no29bo29bo10$72b3o$72bo2bo$72bo$72bo$73bobo$51bobo$50bo2bo$40bo8b2o10b\n2o$39bobo5b2o3bo8b2o$27b2o10b2obo6b2o5b2o$27b2o10b2ob2o6bo2bo4bo$39b2o\nbo8bobo$39bobo$40bo9bo$51bo$49b3o5$o$58bo$56bobo$57b2o7$72b3o$o2bo26bo\n2bo38bo2bo$4bo29bo37bo$o3bo25bo3bo37bo$b4o26b4o38bobo4$38b3o16b2o$40bo\n16b2o$39bo3$64b2o$56b3o4bobo$31b2o23b3o4bobob2o$30bobo22bo3bo4bobobo$\n32bo33bo$10b2o42b2o3b2o4b2o$10b2o52b3o$o9b2o52b3o$11bo52b3o$10bobo52b\n2o$10bobo10b3o28b3o9bo$11bo13bo32b2o4bobobo11b2o$24bo33b2o3bobob2o11b\n2o$59b2o2bobo$8b2o3b2o42bobo4b2o$8bobobobo42b2o$9b5o$10b3o3b2o54b3o$\n11bo3bobo34b2o3b2o13bo2bo4b3o$17bo34b2o3b2o13bo6b2ob2o$64bo7bo6b2ob2o$\n54b3o8b2o6bobo3b5o$54b3o7b2o12b2o3b2o$55bo2$78bo$12b3o61b2obo$11b2ob2o\n63bo$11b2ob2o$11b5o42bo17bob2o$10b2o3b2o39b2ob2o7b2o8bo2bo$69b2o8bobo$\n55bo5bo6bo2$55b2obob2o$14b2o$78b3o$o60b2o14bo3bo$60bobo13bo5bo$12b2o\n47bo15bo3bo$12b2o46b2o16b3o$60b3o15b3o$61b2o$59bo2$78b2o$78b2o$60bo$\n59b3o$58b5o$57b2o3b2o$58b5o$58bo3bo$59bobo$60bo3$60b2o$60b2o!\n",
    },
    {
        name: "And_Not_NW_W",
        input: [[[5, 4], "W"], [[4, 5], "N"]],
        output: [[[-1, 4], "W"]],
        height: 3,
        width: 3,
        drawing: "---r--iri--ro--",
        content: "\no29bo29bo13$71bo$69b3o$58b3o7bo$56bo11b2o$54bobo2bo$64bo$53bob4o4bobo$\n52bo2b3o4bo2bo$54bo8b2o$51bo2bo$51bo13b2o$52bo12bobo$49b3o13bo$49bo4$o\n58bo3$52bobo$52b2o$53bo14b2o15b2o$65bo3bo15bo$64bobo2bobo11bobo$64bobo\n3b2o11b2o$62b3ob2o8b2o$61bo13b2obo$62b3ob2o8bobo$64bob2o9bo3$25b2o34b\n2o2b2o$26bo34bo2bobo$26bobo33bobo$27b2o8bobo21b2ob2o13b2o$37b2o25bo14b\no$38bo25bobo13b3o$31b2o32b2o15bo$30bo2bo$31bobo$32bo2$27bo$27b3obo$28b\n2obo$29bob2o$o27b2o14bo$29bobo13bo$29b3obo9b3o$31b4o$34b3o$35bobo$37bo\n$37b2o3$72b3o$72bo2bo$72bo$72bo$73bobo$55b4o26b4o$55bo3bo25bo3bo$55bo\n29bo$56bo2bo26bo2bo3$64b2o$64bobo$66bo$66b2o!\n",
    },
    {
        name: "And_Wire_Wire_EWN_EWN",
        input: [[[-1, 4], "E"], [[7, 2], "W"], [[0, 5], "N"]],
        output: [[[7, 4], "E"], [[-1, 2], "W"], [[0, -1], "N"]],
        height: 3,
        width: 4,
        drawing: "o---r-ior---irio-",
        content: "\no29bo29bo29bo3$2bo$2b3o$5bo$4b2o5$80bo$78b4o$72b2o3bobob2o14b2o$72b2o\n2bo2bob3o11bo2bo7bo$77bobob2o11bo7b2o3bo$78b4o12bo6bo5bo$80bo5bo7bo7b\n5o$85bo9bo2bo$85b3o9b2o6$78bo$78bobo$78b2o3$o29bo29bo$87bo$86b2o10b2o$\n86bobo9b2o4b3o$81b2o12b2o6b5o$79bo3bo10b3o5bo3bobo$78bo5bo10b2o6bo3b2o\n$73b2o2b2obo3bo13b2o$73b2o3bo5bo13b2o$79bo3bo$12b3o48bo17b2o$12bo2bo\n47bobo$12bo50b2o$12bo$13bobo$85b4o26b4o$85bo3bo25bo3bo$85bo29bo$86bo2b\no26bo2bo7$54b2o$54bobo$54bo11bo$64bobo$51b2o9b2o$o43b3o4b2o9b2o12b2o\n12bo$43b5o6b2o6b2o12b2o$42bobo3bo5b3o7bobo$42b2o3bo6b2o10bo$51b2o$51b\n2o6$o2bo26bo2bo26bo2bo26bo2bo$4bo29bo29bo29bo$o3bo25bo3bo25bo3bo25bo3b\no$b4o26b4o26b4o26b4o!\n",
    },
    {
        name: "Duplicate_E_ES",
        input: [[[-1, 4], "E"]],
        output: [[[5, 4], "E"], [[2, 5], "S"]],
        height: 3,
        width: 3,
        drawing: "---r--or-o-ri--",
        content: "\no29bo2$58b2o$58b2o11$40b2o14b2o3b2o$40b2o16b3o$26b2o29bo3bo$6b2o18b2o\n30bobo$6b2o51bo5$60b3o$54bobo$37b2o3b2o10b2o4bobo$25b3o27bo3b5o$7bo16b\no3bo9bo3bo15b2o3b2o$6b3o14bo5bo9b3o16b2o3b2o$5b5o13bo5bo9b3o$4b2o3b2o\n15bo$5b5o14bo3bo19bo$5bo3bo15b3o18b2o12b2o$6bobo17bo20b2o$7bo$38bo5bo\n6b2o$27b3o7b3o5bo4b2o$5bo21b3o7b3o3b3o6bo$3b2ob2o18bo3bo$12bo7bobo12b\n2o3b2o19b2obob2o$2bo5bo4bo6b2o3b2o3b2o3b2o3b2o19bo5bo$11b3o7bo40bo3bo$\n2b2obob2o50bo3b3o$38bo19b2o$37bobo18bobo$36b2o6bobo$36b2o9bo6b2o$20bo\n15b3o8bo6bobo$18bobo16bobo4bo2bo3b2obobo$19b2o17b2o5b3o3bobobo$28b2o\n23bo8bo$4b2o22b2o23b2o7bo$4b2o47b3o5bobo$53b3o4b2ob2o$53b3o3bo5bo$53b\n2o7bo$53bo5b2o3b2o$51bobobo$51b2obobo$54bobo6bo$54b2o7bo$64bo$35bo$33b\nobo$34b2o25b2o$61b2o6$o2bo26bo2bo$4bo29bo$o3bo25bo3bo$b4o26b4o!\n",
    },
    {
        name: "Duplicate_E_EN",
        input: [[[-1, 2], "E"]],
        output: [[[7, 2], "E"], [[4, -1], "N"]],
        height: 4,
        width: 4,
        drawing: "--o-r-o--r----r--i-",
        content: "\no29bo29bo29bo10$72b3o$72bo2bo$72bo$72bo$73bobo$84b2o$84b2o3$87bo$86bo$\n86bo3$82b2o3b2o$85bo$82bo5bo$83b2ob2o$84bobo$85bo$o84bo4$87b2o$87bo$\n88b3o$78b3o9bo$80bo$79bo$72b3o$o2bo26bo2bo26bo2bo8bo2bo$4bo29bo29bo7bo\n$o3bo25bo3bo25bo3bo7bo$b4o26b4o26b4o8bobo5$38bo$36b4o$27b2o5b4ob2o9b2o\n$25bo2bo3bo3b2ob3o8b2o11b3o$16b2o6bo7bo3b2ob2o24bo$16b2o6bo6bo3b5o24bo\n$24bo7b3o3bo49b2o$25bo2bo59b2o$27b2o2$40bo$o40b2o38b2o$40b2o39bobo$35b\n2o41b2obobo$35b2o41bobobo$35b2o43bo$36bo42b2o5b2obob2o$35bobo40b3o$35b\nobo10b3o27b3o5bo5bo$36bo13bo27b3o$49bo29b2o6b2ob2o$72b3o5bo8bo$33b2o3b\n2o25b2o5bo2bo2bobobo$33bobobobo25b2o5bo5b2obobo$34b5o33bo8bobo$35b3o3b\n2o30bobo5b2o$36bo3bobo20bo$42bo21bo21bo$64bo19b2o4b3o$85b2o2bo3bo2$62b\n2o3b2o19bo5bo$65bo22b2o3b2o$62bo5bo2b2o$37b3o23b2ob2o2bobo$36b2ob2o23b\nobo5bo4bobo$36b2ob2o24bo11b2o$36b5o24bo8bo3bo$35b2o3b2o31b2o$73bobo2$o\n66bo$66b3o$39b2o24bo3bo$64bob3obo14b2o3b2o$65b5o11b2o3b5o$80b2o4b2ob2o\n$37b2o43bo3b2ob2o$37b2o48b3o5$85b3o$85b3o$84bo3bo$67b2o14bo5bo$67b2o\n15bo3bo$85b3o10$85b2o$85b2o!\n",
    },
    {
        name: "Duplicate1_E_ENS",
        input: [[[-1, 4], "E"]],
        output: [[[9, 4], "E"], [[6, -1], "N"], [[2, 9], "S"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no29bo59bo29bo2$58b2o$58b2o11$40b2o14b2o3b2o$40b2o16b3o$26b2o29bo3bo$6b\n2o18b2o30bobo$6b2o51bo5$60b3o$54bobo$37b2o3b2o10b2o4bobo$25b3o27bo3b5o\n$7bo16bo3bo9bo3bo15b2o3b2o$6b3o14bo5bo9b3o16b2o3b2o$5b5o13bo5bo9b3o$o\n3b2o3b2o15bo$5b5o14bo3bo19bo$5bo3bo15b3o18b2o12b2o$6bobo17bo20b2o$7bo$\n38bo5bo6b2o$27b3o7b3o5bo4b2o$5bo21b3o7b3o3b3o6bo$3b2ob2o18bo3bo$12bo7b\nobo12b2o3b2o19b2obob2o$2bo5bo4bo6b2o3b2o3b2o3b2o3b2o19bo5bo34b3o$11b3o\n7bo40bo3bo35bo2bo$2b2obob2o50bo3b3o36bo$38bo19b2o42bo$37bobo18bobo42bo\nbo$36b2o6bobo67b2o$36b2o9bo6b2o58b2o$20bo15b3o8bo6bobo$18bobo16bobo4bo\n2bo3b2obobo$19b2o17b2o5b3o3bobobo61bo$28b2o23bo8bo53bo$4b2o22b2o23b2o\n7bo53bo$4b2o47b3o5bobo$53b3o4b2ob2o$53b3o3bo5bo46b2o3b2o$53b2o7bo52bo$\n53bo5b2o3b2o46bo5bo$51bobobo57b2ob2o$51b2obobo57bobo$54bobo6bo51bo$o\n53b2o7bo51bo$64bo$35bo$33bobo$34b2o25b2o54b2o$61b2o54bo$118b3o$108b3o\n9bo$110bo$109bo$102b3o$o2bo26bo2bo26bo2bo26bo2bo8bo2bo14bo2bo$4bo29bo\n29bo29bo7bo21bo$o3bo25bo3bo25bo3bo25bo3bo7bo17bo3bo$b4o26b4o26b4o26b4o\n8bobo15b4o8$93b3o$95bo$94bo$118b2o$118b2o4$o110b2o$111bobo$108b2obobo$\n108bobobo$110bo$109b2o5b2obob2o$108b3o$60b2o16b3o27b3o5bo5bo$60b2o18bo\n3b2o22b3o$79bo4b2o23b2o6b2ob2o$102b3o5bo8bo$95b2o5bo2bo2bobobo$95b2o5b\no5b2obobo$102bo8bobo$60b3o8b2o11bo18bobo5b2o$59b2ob2o6b6o6b2ob2o6bo$\n59b2ob2o8bob2o18bo21bo$59b5o7bobo7bo5bo6bo19b2o4b3o$58b2o3b2o50b2o2bo\n3bo$81b2obob2o$92b2o3b2o19bo5bo$64bo30bo22b2o3b2o$63bob2o13b2o10bo5bo\n2b2o$63bo16bobo10b2ob2o2bobo$81bo12bobo5bo4bobo$63b2obo14b2o12bo11b2o$\n61bo2bo15b3o12bo8bo3bo$61bobo16b2o21b2o$83bo19bobo2$o96bo$96b3o$62b3o\n17bo12bo3bo$61bo3bo15b3o10bob3obo14b2o3b2o$60bo5bo13b5o10b5o11b2o3b5o$\n61bo3bo13b2o3b2o24b2o4b2ob2o$62b3o15b5o27bo3b2ob2o$62b3o15bo3bo32b3o$\n81bobo$82bo2$62b2o$62b2o18b2o31b3o$82b2o31b3o$114bo3bo$97b2o14bo5bo$\n97b2o15bo3bo$115b3o10$115b2o$115b2o!\n",
    },
    {
        name: "Duplicate_N_WEX",
        input: [[[2, 11], "N"]],
        output: [[[-1, 6], "W"], [[7, 0], "EX"]],
        height: 6,
        width: 4,
        drawing: "----ro-----r--i-r--o---",
        content: "\no59bo29bo$28b2o$28bo2bo$14bobo15bo$12bo3bo2b3o10bo6b2o$12bo19bo6b2o$5b\n2o4bo4bo7b2o2bo2bo$5b2o5bo7bobo2bo2b2o$12bo3bo5b3o$14bobo$28bo2bo$7b2o\n23bo11b4o$7b2o19bo3bo10bo3bo$29b4o14bo$43bo2bo$7bo$6b3o10bo$5bo3bo9b2o\n18b2o2b3o2b2o$7bo10bobo18bo2b5o2bo$4bo5bo29b9o$4bo5bo20bo5b3o9b3o$5bo\n3bo20b2o5bo2bo7bo2bo$6b3o21bobo5b2o9b2o$89bo$11b2o74b3o$12b2o72bo$11bo\n27bo7bo38b2o$38b4o5bobo$33b2o2bo2b2o8b2o4b2o$33b2o2b2o11b2o4b2o25b3o$o\n21b2o6b2o10bo7b2o31b3o$22b2o5b3o10bo4bobo24bo7bo3bo$9bo20b2o10bo4bo25b\n2o$8b3o22b2o38bobo5b2o3b2o$8b3o22b2o2$6b2o3b2o$6b2o3b2o3$9bo$8bobo$7b\n2o77b2o$7b2o77bo$7b3o77b3o$8bobo78bo$9b2o2$74b3o$76bo$75bo10$o3$59b3o$\n61bo$60bo13$44b3o$46bo$45bo4$30b2o15b2o$31bo15bo3bo$31bobo11bobo2bobo$\n32b2o11b2o3bobo$39bo9b2ob3o$38bobo14bo$o37bobo8b2ob3o$3b2o19b2o13bo9b\n2obo$4bo19bo$4bobo7b2o6bobo$5b2o6bobo5b3o26b2o2b2o$12bo6b3o28bobo2bo\n21bo$12bo2bo2bo2bo30bobo22b2o$12bo6b2o15b2o13b2ob2o16b2o4b2o13b2o5bo$\n13bobo21bo14bo15b2o2b2o4b3o11b3o3bo3bo$14b2o6b3o9b3o13bobo15b2o2b2o4b\n2o9bob2o5bo$22bo11bo7b3o5b2o25b2o10bo2bo4bo5bo$23bo18bo2bo31bo11bob2o\n9b2o$42bo38bo10b3o$42bo38bobo9b2o$43bobo25bo2bo6b2o$25b4o26b4o11bo$25b\no3bo25bo3bo10bo3bo$25bo29bo14b4o12bo$26bo2bo26bo2bo25b2o$85bobo2$59b2o\n2b3o2b2o10bo$59bo2b5o2bo10b2o$60b9o10bobo$37b3o17b3o9b3o$37bo19bo2bo7b\no2bo21b2o$38bo19b2o9b2o21b2o10bobo$94bo8bo2bo$89b2o11b2o10b2o$61b2o9b\n2o15bobo8b2o3bo8b2o$o60bobo9b2o9b2o6bo9b2o5b2o$52b3ob2o4b3o7bo6bo3bo2b\no2bo2bo10bo2bo4bo$52b4o2bo4b3o12bobo3b2o6bo11bobo$56b2o4b3o12bo3b2o6bo\nbo$61bobo13bo3b2o6b2o$61b2o14bo3b2o$78bobo$79bo2$52b3o$42b3o7bo$42bo2b\no7bo$42bo$42bo$43bobo8$51b2o$51b2o$67b3o$67bo$68bo4$o$75b2o$59b2o14bob\no9b2o5bo$60b2o13bo10b3o3bo3bo$50b5o4bo11bo11bob2o5bo$49bob3obo15b2o10b\no2bo4bo5bo$50bo3bo11b2o4b2o9bob2o9b2o$51b3o8b2o2b2o4b3o11b3o$52bo9b2o\n2b2o4b2o13b2o$53b2o16b2o$42b3o8bobo15bo$42bo2bo7bobo$42bo11bo$42bo$43b\nobo$51b2obob2o$51bo5bo$52bo3bo$53b3o8$53b2o$53b2o!\n",
    },
    {
        name: "Duplicate2_E_ENS",
        input: [[[-1, 4], "E"]],
        output: [[[9, 4], "E"], [[2, -1], "N"], [[6, 9], "S"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no29bo29bo29bo2$118b2o$118b2o11$100b2o14b2o3b2o$100b2o16b3o$86b2o29bo3b\no$66b2o18b2o30bobo$66b2o51bo5$120b3o$114bobo$97b2o3b2o10b2o4bobo$85b3o\n27bo3b5o$67bo16bo3bo9bo3bo15b2o3b2o$66b3o14bo5bo9b3o16b2o3b2o$65b5o13b\no5bo9b3o$64b2o3b2o15bo$65b5o14bo3bo19bo$65bo3bo15b3o18b2o12b2o$66bobo\n17bo20b2o$67bo$98bo5bo6b2o$87b3o7b3o5bo4b2o$65bo21b3o7b3o3b3o6bo$63b2o\nb2o18bo3bo$72bo7bobo12b2o3b2o19b2obob2o$42b3o17bo5bo4bo6b2o3b2o3b2o3b\n2o3b2o19bo5bo$42bo2bo25b3o7bo40bo3bo$42bo19b2obob2o50bo3b3o$42bo55bo\n19b2o$43bobo51bobo18bobo$54b2o40b2o6bobo$54b2o40b2o9bo6b2o$80bo15b3o8b\no6bobo$78bobo16bobo4bo2bo3b2obobo$57bo21b2o17b2o5b3o3bobobo$56bo31b2o\n23bo8bo$56bo7b2o22b2o23b2o7bo$64b2o47b3o5bobo$113b3o4b2ob2o$52b2o3b2o\n54b3o3bo5bo$55bo57b2o7bo$52bo5bo54bo5b2o3b2o$53b2ob2o53bobobo$54bobo\n54b2obobo$55bo58bobo6bo$55bo58b2o7bo$124bo$95bo$93bobo$57b2o35b2o25b2o\n$57bo63b2o$58b3o$48b3o9bo$50bo$49bo$42b3o$o2bo26bo2bo8bo2bo14bo2bo26bo\n2bo26bo2bo$4bo29bo7bo21bo29bo29bo$o3bo25bo3bo7bo17bo3bo25bo3bo25bo3bo$\nb4o26b4o8bobo15b4o26b4o26b4o8$33b3o$35bo$34bo$58b2o$58b2o4$51b2o$51bob\no$48b2obobo$48bobobo$3b2o45bo$3b2o22b2o20b2o5b2obob2o$27b2o19b3o$18b3o\n27b3o5bo5bo$20bo27b3o$19bo29b2o6b2ob2o$42b3o5bo8bo$35b2o5bo2bo2bobobo$\n35b2o5bo5b2obobo$42bo8bobo$11b2o30bobo5b2o$10bobo6b2o12bo$b2o3b2o4bo5b\n2o14bo21bo$3b3o14bo4b5o4bo19b2o4b3o$2bo3bo17bob3obo24b2o2bo3bo$3bobo\n19bo3bo$4bo21b3o3b2o3b2o19bo5bo$27bo7bo22b2o3b2o$5b3o17b2o5bo5bo2b2o$\n5b3o16bobo6b2ob2o2bobo$24bobo7bobo5bo4bobo$25bo9bo11b2o$35bo8bo3bo$3b\n2o3b2o33b2o$4b5o13b2obob2o14bobo$5b3o14bo5bo$6bo16bo3bo9bo$24b3o9b3o$\n35bo3bo$34bob3obo14b2o3b2o$35b5o11b2o3b5o$50b2o4b2ob2o$52bo3b2ob2o$57b\n3o$5b2o$5b2o18b2o$25b2o2$55b3o$55b3o$54bo3bo$37b2o14bo5bo$37b2o15bo3bo\n$55b3o10$55b2o$55b2o!\n",
    },
    {
        name: "U_turn_W_E",
        input: [[[7, 0], "W"]],
        output: [[[7, 2], "E"]],
        height: 2,
        width: 4,
        drawing: "----rior----r--",
        content: "\no29bo29bo29bo3$67bo$66bobo$49b2o14bo3b2o3b2o$49bobo13bo3b2o3b2o$40b3ob\n2o4b3o12bo3b2o$40b4o2bo4b3o12bobo$8b2o34b2o4b3o7bo6bo$8b2o39bobo9b2o$\n49b2o9b2o4$85b4o26b4o$85bo3bo25bo3bo$67bobo15bo29bo$68b2o16bo2bo26bo2b\no$68bo2$5b2o3b2o18bo$7b3o18bobo$6bo3bo16bobo17bo$7bobo11b2o3bo2bo16b2o\n27bo$8bo12b2o4bobo15b2o4b2o23b2o$28bobo13b3o4b2o2b2o18b2o$30bo4bobo7b\n2o4b2o2b2o$35b2o9b2o$36bo10bo$o4b3o82bo$11bobo$5bobo4b2o68bobo$4b5o3bo\n24b2o9b2o33b2o$3b2o3b2o19bo6bo2bo7bo2bo32bo$3b2o3b2o17b2o7b3o9b3o$28b\n2o9b9o$38bo2b5o2bo$6bo12bo18b2o2b3o2b2o$4b2o14b2o68bo$19b2o70b2o$3bo\n26bo2bo26bo2bo26b2o$34bo29bo$4bo2bo22bo3bo25bo3bo$6b2o23b4o26b4o2$12b\n2o$10bo3bo5bo2b3o71bobo$4b2o3bo5bo9bo3bo68b2o$4b2o2b2obo3bo8bo4bobo66b\no$9bo5bo16b2o4b2o$10bo3bo17b2o4b2o$12b2o18b2o$29bobo71b2o$29bo73bo$\n104b3o$106bo!\n",
    },
    {
        name: "U_turn2_W_E",
        input: [[[7, 2], "W"]],
        output: [[[7, 0], "E"]],
        height: 2,
        width: 4,
        drawing: "----roir----r--",
        content: "\no59bo29bo2$30bo$29bobo$12b2o15b2obo$12bobo14b2ob2o3b2o71b2o$7b2o6bo13b\n2obo4b2o71bo$3b2obo2bo2bo2bo13bobo76bobo$3b2o2b2o6bo8bo5bo77b2o$12bobo\n7bobo$12b2o9b2o$30bo2bo26bo2bo26bo2bo$5b2o27bo29bo29bo$5b2o23bo3bo25bo\n3bo25bo3bo$31b4o26b4o26b4o$19bo$19b2o$3b2o13bobo$37b2o7b2o$27bo9bo9bo$\n26b2o10b9o$26bobo6b3o2b5o2b3o$2b2o3b2o26bo2bo2b3o2bo2bo$3b5o3b2o23b2o\n9b2o$3b2ob2o4b2o$3b2ob2o3bo$4b3o$34b2o9b2o40b2o$33b2o9bobo41b2o$28bo6b\no7b3o4b2ob3o31bo$o26bobo12b3o4bo2b4o$6b3o11b2o3b2o3bo12b3o4b2o$6b3o11b\n2o3b2o3bo13bobo$5bo3bo15b2o3bo14b2o$4bo5bo16bobo50bo$5bo3bo18bo51b2o$\n6b3o70bobo6$72b2o$73b2o$72bo$85b4o26b4o$7b2o76bo3bo25bo3bo$7b2o76bo29b\no$86bo2bo26bo2bo$65bo$53b2o10b2o$46b3o4b2o9bobo$45b5o6b2o12b2o$44bobo\n3bo5b3o10bo3bo$44b2o3bo6b2o10bo5bo$53b2o13bo3bob2o2b2o$53b2o13bo5bo3b\n2o$69bo3bo$70b2o!\n",
    },
    {
        name: "Fork_Not_WN_WN",
        input: [[[7, 2], "W"]],
        output: [[[2, -1], "N"], [[-1, 2], "W"]],
        height: 4,
        width: 4,
        drawing: "-o--r-i-r--l-r--r--o-",
        content: "\no29bo29bo29bo$67bo$66bobo$54b2o9bo3b2o6b2o$54b2o9bo3bob2o4bobo$65bo3bo\nb3o4b3o7b2o$66bobob2o2bo4b3o6b2o$67bo4b2o4b3o$77bobo$77b2o2$64bo$64bob\no$64b2o8$80bo$73b2obo3b4o$67b2o2b2obobo4b4o$66bobo2b2obob2o3bo2bo5b2o$\n65b3o8b2o3b4o5b2o$49bo6b2o6b3o8b2o3b4o$49bobo4b2o7b3o12bo$49b2o15bobo$\n67b2o$o29bo10$42b3o$42bo2bo$42bo$42bo23b2o$43bobo20bobo$55b4o7bo18b4o\n26b4o$55bo3bo25bo3bo25bo3bo$55bo29bo29bo$56bo2bo26bo2bo26bo2bo3$91bobo\n$89bo3bo$82b2o5bo19bo$82b2o4bo4bo14b4o$26b2o61bo12bo4b2obobo3b2o$26b2o\n61bo3bo3bob2o5b3obo2bo2b2o$91bobo2bob4o5b2obobo$81b2o13b2o2b2o6b4o$81b\nobo25bo$o80bo$34b2o$33bobo$33bobob2o50b2o$34bobobo50b2o$25b3o8bo52bobo\n$24bo3bo6b2o51b3o$23bo5bo4b3o51b2obo$23bo5bo4b3o52bo$26bo7b3o$24bo3bo\n6b2o5b3o$25b3o8bo5bo2bo$26bo7bobobo3bo7b2o44bo2bo8bo$33bobob2o3bo7b2o\n44bo10bobo$33bobo7bobo46bo2bo3b2o5bo3b2o$23b3o8b2o53b4o3b2obobo4bo3b2o\n3b2o$23b3o62b4o14bo3b2o3b2o$22bo3bo54b2o5bo2bo8b2o5bobo$30bobo48b2o5b\n4o16bo$21b2o3b2o3b2o56b4o$31bo60bo2$48b2obob2o$43b3o$43bo4bo5bo$38bo5b\no$39b2o8b2ob2o$38b3ob2o7bo$43b2o$24b2o16bo$o23b2o23bo10bo29bo$48bobo$\n47bo3bo$47b5o$35bo10b2o3b2o$35b2o10b5o$34bobo11b3o$49bo3$19bo7bo$17bob\no5b4o$9b2o4b2o8b2o2bo2b2o$9b2o4b2o11b2o2b2o$15b2o7bo10b2o6b2o$17bobo4b\no10b3o5b2o$19bo4bo10b2o11b2o$32b2o14b2o$32b2o!\n",
    },
    {
        name: "And_Wire_ES_ES",
        input: [[[-1, 4], "E"], [[2, -1], "S"]],
        output: [[[3, 4], "E"], [[2, 5], "S"]],
        height: 3,
        width: 2,
        drawing: "",
        content: "\no29bo15$44bobo$47bo$47bo$44bo2bo$29b2o14b3o$9b2o18b2o$9b2o18b2o$29bo$\n10bo17bobo$9bobo16bobo$9bobo17bo$10bo2$26b2o3b2o$7b2obob2o12bobobobo$o\n6bo5bo13b5o$8bo3bo15b3o$9b3o17bo7$12bo13bobo$13bo12b2o$11b3o13bo3$30b\n3o$29bo3bo10bobo$6b5o17bo5bo12bo$5bob3obo8bo8bo3bo13bo$6bo3bo7bobo9b3o\n11bo2bo$7b3o9b2o9b3o12b3o$8bo3$31b2o$7b2o22b2o$7b2o5$o2$35bo$33bobo$\n34b2o7$o2bo26bo2bo$4bo29bo$o3bo25bo3bo$b4o26b4o6$51b2o$51bo$52b3o$54bo!\n",
    },
    {
        name: "And_ES_S",
        input: [[[-1, 2], "E"], [[2, -1], "S"]],
        output: [[[2, 3], "S"]],
        height: 2,
        width: 2,
        drawing: "",
        content: "\no29bo12$27bo$25bobo$15b2o6b2o12b2o$14bo3bo4b2o12b2o5bobo$3b2o8bo5bo3b\n2o22bo$3b2o8bo3bob2o4bobo19bo$13bo5bo7bo16bo2bo$14bo3bo26b3o$15b2o$26b\no$27b2o$26b2o6$33bobo$34b2o$17bob2o4bo8bo$17b2obo3bobo$24bobo$15b5o3b\n2ob3o$14bo2bo2bo8bo$14b2o3b2o2b2ob3o12bo$23b2obo15b2o$30bo10b2o$28b3o$\n27bo$o2bo23b2o$4bo$o3bo$b4o16bo26bobo$20b3o7b2o17b2o$19bo2bo6bobo17bo$\n19b3o9bo$20bo32b2o$16b2o35bobo$15bobo37bo$15bo39b2o$14b2o$27b2o$27bo$\n28b3o$30bo!\n",
    },
    {
        name: "And_EN_N (Illegal)",
        input: [[[-1, 2], "E"], [[2, 3], "N"]],
        output: [[[2, -1], "N"]],
        height: 2,
        width: 2,
        drawing: "",
        content: "\no$6b2o19b2o$6b2o19b2o3$33bo23bo$33b3o19b3o$6b3o18bo8bo17bo$6b3o18bo7b\n2o17b2o$5bo3bo16bobo$25b2ob2o$4b2o3b2o13bo5bo$27bo$24b2o3b2o2$49b2obob\n2o$4b3o19b4o$8b2o15b2o2bo19bo5bo$8b2o15b2obo$9b2o39b2ob2o$7bobo16b2o\n24bo$7b2o17bo3$2b2o3b2o17b2obob2o21b2o$2b2o3b2o11bo5bo5bo21bo$14bo4bo\n7bo3bo14b2o7b3o$4b3o8b2o2b3o6b3o14bobo9bo$4b3o7b2o31bo$5bo$o4$21bobo$\n4b2o16b2o5b2o$4b2o16bo6b2o5$o2bo27b2o$4bo25bobo$o3bo27bo$b4o5$23b3o$\n12bo12bo$7bo4b4o8bo$7bo5b4o10b2o$2b2o9bo2bo9bobo$2b2o9b4o8b3o4b2o$12b\n4o8b3o4bo2b4o$12bo12b3o4b2ob3o$26bobo$27b2o!\n",
    },
    {
        name: "And_EN_N (Illegal 2)",
        input: [[[-1, 2], "E"], [[0, 3], "N"]],
        output: [[[0, -1], "N"]],
        height: 2,
        width: 2,
        drawing: "",
        content: "\no29b2o$30b2o$49b2o$49b2o4$31bo$30b3o$30b3o2$28b2o3b2o$28b2o3b2o13b3o$\n47bo3bo$46bo5bo$30b2o14bo5bo$30bobo16bo$29bo2b2o13bo3bo$31b2o15b3o$31b\n2o16bo$32bo2$26bo5bo17b3o$26bo5bo5bobo9b3o$5b2o20bo3bo6bobo8bo3bo$6bo\n21b3o8bo3bobo$6bobo34b2o3b2o3b2o$7b2o35bo3$o4$28b2o$28b2o$51b2o$51b2o$\n20b2o$20bobo$12b3o5bo7bobo$o2bo8bo2bo12b2o$4bo7bo16bo$o3bo7bo$b4o8bobo\n2$27b3o$27bo$28bo2$41b2o$36bo4b2o$30b2ob5o6b2o$29bo4b2o2bo5b3o5b2o$28b\no8b2o5b2o6b2o$18b2o8bo7bo4b2o$18b2o8bo12b2o$29bo$30b2o!\n",
    },
    {
        name: "And_EN_N",
        input: [[[-1, 2], "E"], [[0, 5], "N"]],
        output: [[[0, -1], "N"]],
        height: 3,
        width: 2,
        drawing: "",
        content: "\no24$5b2o$6bo$6bobo$7b2o3$o29bo29bo8$20b2o$20bobo$12b3o5bo$o2bo8bo2bo$\n4bo7bo$o3bo7bo$b4o8bobo3$47b2o$47b2o$24b2o$24b2o2$25bo21bo$24bobo8b2o\n9b3o$24bobo8bobo7bo3bo$25bo9bo8bob3obo$45b5o2$22b2obob2o$22bo5bo$23bo\n3bo$24b3o3bo11b3o$30b2o10bo$29bobo11bo6$27bo$12b3o12bo16b3o$12bo2bo10b\nobo14bo3bo$12bo12b2ob2o12bo5bo$12bo11bo5bo11b2obob2o$13bobo11bo$24b2o\n3b2o$45bo$44bobo$28bo15bobo$28bo16bo$29bo$45b2o$45b2o$26b2o$26b2o6$60b\no!\n",
    },
    {
        name: "And_NN_NN",
        input: [[[2, 3], "N"], [[6, 3], "N"]],
        output: [[[2, -1], "N"], [[6, -1], "N"]],
        height: 2,
        width: 4,
        drawing: "",
        content: "\no29bo29bo29bo5$112b2o$112bo$110bobo$110b2o$52b2o$53bo52b2o$53bobo6b2o\n41bobo$54b2o6b3o42bo$64b2obo$64bo2bo$64b2obo$62b3o6b2o$62b2o7bobo$73bo\n$73b2o3$63bo$47b2o15b2o$46bobo14b2o$29b2o17bo42b2o$28bo3bo57bobo$12b2o\n13bo5bo3b2o53bo$12b2o13bo3bob2o2b2o$3b2o3bo6b2o10bo5bo$3bobo3bo5b3o10b\no3bo$4b5o6b2o12b2o$5b3o4b2o9bobo$12b2o10b2o$24bo$94bo$92b3o$91bo$32b2o\n57b2o$31bobo45b2o9b2o$33bo45bo9b2o$81bo4bo3bo$80bo3b3ob3o$80bo8bo$84b\n6o$74b2o8b2obo$24b3o48bo7b2o$26bo45b3o$25bo46bo$13bo$12b2o$11b2o4b2o5b\no$b2o7b3o4b2o3bobo$b2o8b2o4b2o2bobo$12b2o6bo2bo11b2o$13bo7bobo11b2o$\n22bobo$24bo!\n",
    },
    {
        name: "And1_NN_NN",
        input: [[[0, 3], "N"], [[4, 3], "N"]],
        output: [[[0, -1], "N"], [[4, -1], "N"]],
        height: 2,
        width: 4,
        drawing: "",
        content: "\no29bo29bo29bo2$3b2o$4bo$4bobo$5b2o$63b2o$63bo$54b2o5bobo$10b3o40bo3bo\n3b2o$10bo41bo5bo$11bo40bo3bob2o$52bo5bo$44b2o7bo3bo$43bobo8b2o$43bo$\n42b2o2$53bobo$53b2o$54bo2$69b3o$69bo$25b3o42bo$25bo64b2o$26bo63b3o$81b\n2o9b2obo8bo$81bo5bo4bo2bo6bobo$86bo5b2obo5bobo11b2o$o81bo3bo3b3o7bo2bo\n11b2o$84bo5b2o9bobo$22bo79bobo$22b3o13bobo53bo9bo$25bo12b2o52b2o$24b2o\n13bo53b2o$25b2o$26b2o8b2o46b3o$26bo3bo4bo2bo45bo$26b3ob3o3bobo46bo$27b\no9bo$27b6o$29bob2o8b2o$32b2o7bo$42b3o47b2o$44bo47bobo$92bo3$106bobo$\n101b2o3bo2bo$94b2o2b2ob3o5b2o$93bobo3bo3bo3bo3b2o4b2o$92bo8bobo5b2o6b\n2o$83b2o7bo2bo6b2o2bo2bo$83b2o7bo13bobo$93bobo$94b2o!\n",
    },
    {
        name: "And_Not_And_Not_NNS_N",
        input: [[[8, 7], "N"], [[4, 7], "N"], [[0, -1], "S"]],
        output: [[[8, -1], "N"]],
        height: 4,
        width: 5,
        drawing: "i---or----ri-i--r----",
        content: "\no29bo29bo$92b2o$93bo$93bobo5bo$94b2o3b4o$98bobob2o$7bo15b2o72bo2bob3o$\n7b3o13bobo72bobob2o$10bo14bo73b4o8b2o$9b2o13b2ob2o72bo9bobo$25bobo85bo\n$23bobo2bo84b2o$23b2o2b2o73bo$103bo$13bo87b3o$12bobo7b2obo$11bo3bo6b2o\nb3o$11bo3bo12bo56b2o$11bo3bo6b2ob3o58b2o$5b2o5bobo3b2o3bobo59bo$4bobo\n6bo4bobo2bobo$4bo15bo3bo$3b2o15b2o5$117bo$118bo$116b3o$o2$70b2o$25bo\n45b2o$23bobo44bo$24b2o7$132bo$133bo$131b3o3$55b2o$40bo15b2o$38bobo14bo\n$39b2o3$64b2o$64bo78b2o$55bo6bobo78bobo$55bobo4b2o35b2o44bo$58b2o40bo\n44b2o$58b2o40bobo10bo$58b2o41b2o9bobo$o44b2o8bobo54b2obo$44bobo8bo56b\n2ob2o$44bo67b2obo$43b2o67bobo3b2o$113bo4bobo$120bo$120b2o3$95b3o$97bo\n34b3o$96bo14bobo18bo2bo$112b2o18bo$112bo19bo$133bobo12$126bobo$127b2o$\n127bo2$o6$60b2o15b2o$61bo15bo3bo$61bobo11bobo2bobo$62b2o6bo4b2o3bobo$\n69b3o7b2ob3o$68bo3bo12bo$68bob2o7b2ob3o58b2o$69b2o8b2obo60bobo$145bo$\n145b2o$80b2o2b2o$80bobo2bo$82bobo$66b2o13b2ob2o$67bo14bo$64b3o13bobo$\n64bo15b2o!\n",
    },
    {
        name: "And_Not_NN_NN",
        input: [[[2, 3], "N"], [[6, 3], "N"]],
        output: [[[2, -1], "N"], [[6, -1], "N"]],
        height: 2,
        width: 4,
        drawing: "-o-or--ri-i-r--",
        content: "\no29bo29bo29bo7$110b2o$110bo$52b2o54bobo$53bo54b2o$53bobo6b2o$54b2o6b3o\n$64b2obo$64bo2bo$64b2obo$62b3o6b2o$62b2o7bobo$73bo24b3o$73b2o25bo$99bo\n2$63bo$47b2o15b2o$46bobo14b2o$29b2o17bo42b2o$28bo3bo57bobo$12b2o13bo5b\no3b2o53bo$12b2o13bo3bob2o2b2o$3b2o3bo6b2o10bo5bo$3bobo3bo5b3o10bo3bo$\n4b5o6b2o12b2o$5b3o4b2o9bobo$12b2o10b2o57b3o$24bo60bo$84bo3$32b2o$31bob\no$33bo42b2o24b3o$75bobo24bo2bo$77bo24bo$102bo$103bobo$61bobo$24b3o33bo\n2bo3b2o$26bo32b2o5b3ob2o2b2o$15bo9bo25b2o4b2o3bo3bo3bo3bobo$14bobo34b\n2o6b2o5bobo8bo$14b2obo8bobo31bo2bo2b2o6bo2bo7b2o$2b2o10b2ob2o6bo2bo4bo\n27bobo13bo7b2o$2b2o10b2obo6b2o5b2o41bobo$14bobo5b2o3bo8b2o36b2o$15bo8b\n2o10b2o$25bo2bo$26bobo!\n",
    },
    {
        name: "And_Not1_NN_NN",
        input: [[[0, 3], "N"], [[4, 3], "N"]],
        output: [[[0, -1], "N"], [[4, -1], "N"]],
        height: 2,
        width: 4,
        drawing: "",
        content: "\no29bo29bo29bo6$5b2o$6bo$6bobo54b2o$7b2o54bo$53b2o6bobo$51bo2bo6b2o$50b\no$50bo6bo$50bo7b2o$44b2o5bo2bo$43bobo7b2o$17b2o24bo$17bobo22b2o$17bo2$\n52bobo$52b2o$53bo14b3o$68bo$24b3o42bo$24bo$25bo66bo$92bobo$81b2o12b2o\n6b2o$o80b2o12b2o4bo3bo$95b2o3bo5bo8b2o$32b2o58bobo4b2obo3bo8b2o$32bobo\n57bo7bo5bo$32bo68bo3bo$103b2o$93bo$91b2o$83b3o6b2o$83bo$12b3o24b3o42bo\n$12bo2bo23bo$12bo27bo$12bo$13bobo$91b2o$91bobo$47b2o9b2o31bo$47bobo7bo\nbo$41bo5bo8bo6b2o$40bobo13bo2bo2bo2bob2o36bobo$39bob2o13bo6b2o2b2o31b\n2o3bo2bo$33b2o3b2ob2o14bobo33b2o2b2ob3o5b2o$33b2o4bob2o15b2o32bobo3bo\n3bo3bo3b2o4b2o$40bobo48bo8bobo5b2o6b2o$41bo40b2o7bo2bo6b2o2bo2bo$82b2o\n7bo13bobo$92bobo$93b2o!\n",
    },
    {
        name: "And_Not_NN_N",
        input: [[[0, 3], "N"], [[4, 3], "N"]],
        output: [[[0, -1], "N"], [[4, -1], "N"]],
        height: 2,
        width: 3,
        drawing: "",
        content: "\no6$5b2o$6bo$6bob2o$7bo$11bo$9bo$10bo$71bo$69b3o$58b3o7bo$56bo11b2o$54b\nobo2bo$64bo$53bob4o4bobo$52bo2b3o4bo2bo$54bo8b2o$51bo2bo$51bo13b2o$52b\no12bobo$24b3o22b3o13bo$24bo24bo$25bo3$o3$52bobo$52b2o$23b2o28bo14b2o\n15b2o$22bobo40bo3bo15bo$22bo41bobo2bobo11bobo$21b2o41bobo3b2o11b2o$62b\n3ob2o8b2o$12b3o13bo10b3o19bo13b2obo$12bo2bo12b3o8bo22b3ob2o8bobo$12bo\n18bo8bo23bob2o9bo$12bo17bo$13bobo14bo2bo10bobo$33bo9bo2bo14b2o2b2o$31b\no2b3o6bo3bo13bo2bobo$32bob4o5bo2bo15bobo$44b3o14b2ob2o13b2o$33bobo2bo\n25bo14bo$35bo11b2o15bobo13b3o$37b3o7bo17b2o15bo$48b3o$50bo!\n",
    },
    {
        name: "U_turn_EN_EW",
        input: [[[-1, 4], "E"], [[2, 11], "N"]],
        output: [[[9, 4], "E"], [[-1, 8], "W"]],
        height: 6,
        width: 5,
        drawing: "",
        content: "\no2$88b2o$88b2o11$70b2o14b2o3b2o$70b2o16b3o$87bo3bo$88bobo$89bo2$39b2o$\n39b2o2$40bo49b3o$39bobo42bobo$39bobo25b2o3b2o10b2o4bobo$40bo44bo3b5o$\n68bo3bo15b2o3b2o$69b3o16b2o3b2o$37b2obob2o25b3o$37bo5bo$38bo3bo35bo$\n39b3o34b2o12b2o$77b2o2$68bo5bo6b2o$67b3o5bo4b2o$67b3o3b3o6bo2$42bo22b\n2o3b2o19b2obob2o$43bo21b2o3b2o19bo5bo$41b3o48bo3bo$89bo3b3o$68bo19b2o$\n67bobo18bobo$66b2o6bobo$36b5o25b2o9bo6b2o$35bob3obo8bo15b3o8bo6bobo$\n36bo3bo7bobo16bobo4bo2bo3b2obobo$37b3o9b2o17b2o5b3o3bobobo$38bo44bo8bo\n$83b2o7bo$83b3o5bobo$83b3o4b2ob2o$37b2o44b3o3bo5bo$37b2o44b2o7bo$83bo\n5b2o3b2o$41bo39bobobo$41b2o38b2obobo$40bobo41bobo6bo$o30bo52b2o7bo$30b\nobo61bo$29bo3b2o8bo21bo$18b2o9bo3b2o5b4o4bo14bobo$18b2o9bo3b2o4b4o5bo\n15b2o25b2o$30bobo6bo2bo9b2o37b2o$31bo7b4o9b2o$40b4o$43bo3$30bo2bo26bo\n2bo$34bo29bo$30bo3bo25bo3bo$31b4o26b4o$74bobo$77bo$77bo$74bo2bo7b2o$\n75b3o7b2o10$85b3o$84bo3bo$83bo5bo$84bo3bo$85b3o$85b3o$102bo$101bobo$\n94b2o4bob2o15b2o$94b2o3b2ob2o14bobo$83b3o14bob2o13bo6b2o2b2o$82b2ob2o\n3bo10bobo13bo2bo2bo2bob2o$82b2ob2o4b2o9bo5bo8bo6b2o$82b5o3b2o16bobo7bo\nbo$81b2o3b2o20b2o9b2o2$74bobo$77bo$77bo21bo$74bo2bo7b2o10bo2b2o$75b3o\n20b2o$98bob3o2$83b2o$83b2o3$93bo$93bobo$93b2o2$o5$109b2o$102b3o4b2o$\n62b2o37b5o6b2o10bo$62bo37bobo3bo5b3o7bobo$60bobo37b2o3bo6b2o6b2o$60b2o\n47b2o9b2o12b2o$109b2o9b2o12b2o$122bobo$112bo11bo$101bo2bo7bobo$25b4o\n26b4o15bobo8b4o11bo11b2o$25bo3bo25bo3bo17bo7bo3bo10bo3bo12bo$25bo29bo\n21bo7bo14b4o12b2o$26bo2bo26bo2bo14bo2bo8bo2bo26bobo$75b3o$113bo$47b3o\n41b2o2b3o2b2o11b2o$49bo41bo2b5o2bo10bobo$48bo43b9o$89b3o9b3o20b2o$73b\n2o14bo2bo7bo2bo19b2o$74bo15b2o9b2o22bo9bo$71b3o59bobo$71bo33b2o14b2o9b\nobo11b2o$93bobo10b2o13b3o7bo2bo11b2o$30b2o15b2o44bo2bo8bo11bo5b2obo5bo\nbo$31bo15bo3bo32b2o10b2o11b2o6bo5bo2bo6bobo$31bobo11bobo2bobo31b2o8bo\n3b2o8bobo12b2obo8bo$32b2o11b2o3bobo36b2o5b2o9bo13b3o$39bo9b2ob3o33bo4b\no2bo10bo2bo10b2o$38bobo14bo37bobo11bo$38bobo8b2ob3o53bobo$39bo9b2obo\n56b2o3$42b3o5b2o2b2o$42bo2bo4bobo2bo$42bo9bobo$36b2o4bo8b2ob2o$37bo5bo\nbo6bo$34b3o13bobo$34bo15b2o14$o!\n",
    },
    {
        name: "U_turn_WN_EXN",
        input: [[[7, 0], "W"], [[6, 3], "N"]],
        output: [[[7, 2], "EX"], [[6, -1], "N"]],
        height: 2,
        width: 4,
        drawing: "---oriori---r--",
        content: "\no29bo29bo29bo3$81bo$81b3o$84bo$83b2o$96b2o$8b2o86bo$8b2o84bobo$94b2o6b\n3o$86b2o14bo2bo$6bo78bo2bo13bo$7bo76b2ob2o13bo$7bo77bobo15bobo$86bo28b\n4o$115bo3bo$5b2o3b2o103bo$8bo74b2o31bo2bo$5bo5bo72bo$6b2ob2o20bobo47b\n3o$7bobo20bo2bo47bo$8bo20b2o10bo6bo36bob2o$8bo12b2o4b2o3bo8bo5bobo19bo\n13b3ob2o2b2o3b2o$21b2o6b2o9bo6b2obo18bobo10bo8bo2bo2bo$30bo2bo2b2o9b2o\nb2o3b2o12b2o12b3ob2o3b5o$31bobo2bo2b3o5b2obo4b2o28bobo$36b4o7bobo35bob\no3bob2o$37b2o9bo37bo4b2obo$10bobo$o10b2o$5b3o3bo$4bo3bo21bo6b2o9b2o$3b\no5bo18b2o6bo2bo2b3o2bo2bo$3b2obob2o19b2o5b3o2b5o2b3o$39b9o$18bo19bo9bo\n$6bo12b2o17b2o7b2o$5bobo10b2o$5bobo$6bo21bo2bo70b3o$32bo11b4o26b4o24bo\n2bo$6b2o20bo3bo10bo3bo25bo3bo24bo$6b2o21b4o14bo29bo24bo$43bo2bo26bo2bo\n26bobo$13bo8b2o$11bobo6bo2bo$4b2o4bobo7bo3bo2b2o$4b2o3bo2bo7bo2b2o2b3o\n$10bobo16b2obo5b2o$11bobo4b3o8bo2bo5b2o$13bo15b2obo$27b3o$27b2o!\n",
    },
    {
        name: "Before_Latch_EYN_NN",
        input: [[[-1, 2], "EY"], [[4, 13], "N"]],
        output: [[[0, -1], "N"], [[4, -1], "N"]],
        height: 7,
        width: 4,
        drawing: "o-o-r-------r-i--r-----i-",
        content: "\no29bo29bo29bo$41b2o$21b2o18b2o$21bo2bo2$25bo13bo$40bo$23b2o15bo$22bo2$\n38b2o3b2o27b3o$19b2o3b2o15bo30bo2bo$19b2o3b2o12bo5bo27bo$20b5o14b2ob2o\n28bo$21bobo16bobo30bobo$41bo$21b3o17bo6$25bo11bobo$26bo10b2o$24b3o11bo\n3b3o$20bo11bo8bo3bo$19b3o8b3o7bo5bo$11b3o4b5o5bo4bo6b2obob2o$10bo2bo3b\n2o3b2o4bobo$13bo14bo$o12bo17b3o9bo46bo$10bobo19bo9bobo$19b3o20bobo$19b\n3o21bo2$43b2o$19b2o22b2o$19b2o19bo72b2o$41bo71bo$39b3o69bobo$72b3o36b\n2o$13b4o55bo2bo$12bo3bo55bo$16bo55bo$12bo2bo57bobo6$67b2o$67bo$55bo9bo\nbo$56bo8b2o$54b3o2$61b2o$11b3o46bo2bo$10bo2bo46bobo$13bo27bo19bo$o12bo\n25b3o48bo$10bobo15b3o7bo26bo$26bo11b2o26b2o$24bobo2bo31b3obo$34bo30bo$\n23bob4o4bobo24bo$22bo2b3o4bo2bo26bob2o$24bo8b2o25bob2o$21bo2bo35b2o$\n21bo35b2o$22bo33bobo13b3o$19b3o34bo15bo2bo$19bo35b2o15bo$72bo$73bobo4$\n55b2o$56bo$56bobo$57b3o$59b4o$60bob3o$62bobo$64b2o$61b2obo$11b3o14b2o\n32bob2o$10bo2bo15bo32bob3o$13bo12b3o37bo$o12bo12bo63bo$10bobo48bo$59bo\n2b2o$59b2o4$5b2o58b2o$6bo58bobo$3b3o61bo$3bo63b2o3b3o$72bo2bo$72bo$72b\no$73bobo3$43bo$43b2o$42bobo3$20b2o$20b2o22b2o$44b2o3$11b3o$10bo2bo$13b\no$o12bo19bobo54bo$10bobo20bobo$28bo$18b2o3b2o3b2o5bob2o$27bobo4bo$19bo\n3bo11bo2bo2b2o3b2o$20b3o13b2o5b3o$20b3o19bo3bo$43bobo$44bo42b2o$23bo\n61bo3bo$22b3o16b3o35b2o3bo5bo13b2o$21bo3bo15b3o35b2o2b2obo3bo13b2o$23b\no60bo5bo10b2o6bo3b2o$20bo5bo58bo3bo10b3o5bo3bobo$20bo5bo49b3o8b2o12b2o\n6b5o$21bo3bo13b2o3b2o30bo15bobo9b2o4b3o$22b3o15b5o32bo14b2o10b2o$41b3o\n49bo$42bo2$86bo$85bo3bo$85b5o$88bo$85bobo$22b2o61bobo$11b3o8b2o18b2o\n42b2o$10bo2bo28b2o$13bo$o12bo14b2o61b3o9b2o$10bobo15b2o61bo9bo2bo$86bo\n5bo7bo7b5o$84b4o12bo6bo5bo$83bobob2o11bo7b2o3bo$78b2o2bo2bob3o11bo2bo\n7bo$20b2o56b2o3bobob2o14b2o$20bobo5b3o53b4o$17b2obobo63bo$17bobobo6bob\no$19bo7b5o40b3o$19b2o5b2o3b2o39bo2bo$11b3o5b3o4b2o3b2o39bo$11bo2bo4b3o\n50bo$11bo3bo3b3o51bobo$11bo7b2o8b2o$12bobo4bo7b2ob2o$4b2o11bobobo5bo2b\no$4b2o11b2obobo7bo$20bobo4bo$20b2o6b2o3$28b2o3b2o$23bo5b5o$21b2o7b3o$\n22b2o7bo$3b3o5b3o$2bo3bo3bo2bo$bo5bo5bo$bo5bo2bo2bo$12bo$7bo$6b2o$6b2o\n22b2o$4bo2b2o21b2o$5bobo$5b2o$18b2o$17b2o$3b2o3b2o9bo52b3o$3b2o3b2o62b\no2bo$72bo$5b3o64bo$5b3o65bobo$6bo19bo10bo$25b2o9b2o$20bo4bobo7b2o4b2o\n2b2o$18bobo13b3o4b2o2b2o$11b2o4bobo15b2o4b2o$11b2o3bo2bo16b2o$6b2o9bob\no17bo$6b2o10bobo$20bo!\n",
    },
    {
        name: "-----------",
        input: [[[-1, 4], "E"]],
        output: [[[9, 4], "E"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "!",
    },
    {
        name: "And gate - EN - E",
        input: [[[-1, 4], "E"], [[4, 9], "N"]],
        output: [[[9, 4], "E"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no57$47b2o$48bo$48bobo$49b2o$52b2o$52bobo$52bo8$o2$o$bo2$67b2o$67bobo$\n67bo13$82b2o$82bobo$82bo13$97b2o$97bobo$97bo2$86b2o$85bo2bo$88bo$88bo$\n86bobo11bo3b3o$86bobo11b2o2bo$87bo11bobo3bo3$84b2o3b2o$84bo5bo21bo2bo\n8bo$112bo10bobo$85bo3bo2b2o14bo2bo3b2o5bo3b2o$86b3o4b2o10b4o3b2obobo4b\no3b2o3b2o$92bo11b4o14bo3b2o3b2o$97b2o5bo2bo8b2o5bobo$97b2o5b4o16bo$\n105b4o$108bo2$89bo$87b2ob2o2$86bo5bo2$86b2obob2o9$88b2o$88b2o!\n",
    },
    {
        name: "And gate - ES - E",
        input: [[[-1, 4], "E"], [[4, -1], "S"]],
        output: [[[9, 4], "E"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no3$117b2o$117b2o9$117bo$116b3o$115b5o$114b2o3b2o$115b5o$115bo3bo$116bo\nbo$117bo3$119bo$117b2ob2o$112bo$111bo4bo5bo$111b3o$116b2obob2o$107b2o$\n108bo$107b2o$105bobo3bo$104bo3b2obo$105bobob3o3$113bo5b2o$112b2o5b2o$\n112bobo$97bo$96bo$96b3o$121bo7bo$120b4o5bobo$115b2o2bo2b2o8b2o$115b2o\n2b2o11b2o4b2o$112b2o10bo7b2o4b2o$104b2o5b3o10bo4bobo$104b2o6b2o10bo4bo\n$115b2o$115b2o4$82bo$81bo$81b3o13$67bo$o65bo$66b3o$o$bo11$52bo$51bo$\n51b3o13$38b2o$39bo$36b3o$36bo!\n",
    },
    {
        name: "And gate - EW - N",
        input: [[[9, 4], "W"], [[-1, 4], "E"]],
        output: [[[4, -1], "N"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no20$30b2o$31bo$31bobo5bo$32b2o4bobo$37bob2o15b2o$36b2ob2o16bo$37bob2o\n16bobo$38bobo8b2o7b2o$18bo20bo9bobo$16b3o32bo$15bo35b2o$15b2o23bo$38bo\nbo$39b2o$12b3o$12b3o$11bo3bo7bo$23b2o$10b2o3b2o5bobo8$55bo$10b2o41bobo\n$11bo42b2o$8b3o$8bo24bo$33b3o$36bo$21b3o11b2o$21bo$22bo65b2o$88bobo$\n88bo$38bo$37b3o$36b5o$35bobobobo$35b2o3b2o$121bo$121b3o$38bo85bo$37bob\no83b2o$37bo98b2o$38bo2bo94bo$41bo92bobo$33b2o5bo16b2o13b3o28b2o25bo3b\n2o$o2bo28bo2bo5b3o13b2o13bo2bo27bobo23bobo$4bo29bo8bo28bo30bo25b2o$o3b\no26bo2bo37bo46bo8bo2bo$b4o68bobo43bobo6b2ob2o$31b2o31b2o53b2o7bo3bo12b\n4o$63bobo63b3o13bo3bo$63bobob2o76bo$64bobobo54b2o21bo2bo$66bo57bo$54b\n2obob2o4b2o54b3o$64b3o54bo$3b2o49bo5bo3b3o58bob2o$3b2o59b3o56b3ob2o2b\n2o3b2o$19b2o34b2ob2o5b2o55bo8bo2bo2bo$20b2o35bo8bo5b3o43b2o3b3ob2o3b5o\n$19bo44bobobo2bo2bo5b2o36bobo4bobo$63bobob2o5bo5b2o36bo6bobo3bob2o$30b\n2o31bobo8bo51bo4b2obo$29bobo32b2o5bobo$28b3o52bo18b2o43bo$12bo15b2o30b\no21bo18bobo41b3o$4bo7b2o2b2o10b2o24b3o4b2o19bo18bo42bo$3b3o5bobo2bobo\n10bobo21bo3bo2b2o38b2o42b2o$2b5o9bo13bo$b2o3b2o44bo5bo19b2o3b2o$2b5o\n45b2o3b2o22bo$2b5o20b2o3b2o40b2o2bo5bo$3bo2bo20b2o3b2o40bobo2b2ob2o58b\no$3bo3bo59bobo4bo5bobo58b3o$7bo15b3o3b3o36b2o11bo51b2o5b5o$4b2obo15bo\n5b3o36bo3bo8bo51bobo3bobobobo$6bo17bo5bo41b2o59bo5b2o3b2o$71bobo46bo$\n119b2o$3b2o3b2o69bo23b2o13b2o4b2o2b2o12bo$3bo5bo68b3o22b3o11b3o4b2o2b\n2o11bobo$77bo3bo12b2o9b2obo9b2o4b2o15bo$4bo3bo18b3o25b2o3b2o14bob3obo\n11bo5bo4bo2bo10b2o21bo2bo$5b3o19b3o26b5o3b2o11b5o17bo5b2obo11bo24bo$\n26bo3bo25b2ob2o4b2o28bo3bo3b3o10bo27bo$56b2ob2o3bo32bo5b2o9bobo28b3o$\n25b2o3b2o25b3o55b2o30bo4$5b2o124bo$5b2o52b3o61bo7b2o$59b3o62bo5bobo$\n58bo3bo59b3o$57bo5bo14b2o$58bo3bo15b2o$28b2o29b3o$28b2o$123b2o$124b2o$\n123bo$112b2o$111bo3bo$110bo5bo7bo$100b2o8bo3bob2o4bobo$100b2o8bo5bo3b\n2o$60b2o49bo3bo4b2o12b2o$60b2o50b2o6b2o12b2o$122bobo$124bo$60b2o$61bo$\n61bobo$62b2o10$149bo!\n",
    },
    {
        name: "Or gate - EN - E",
        input: [[[-1, 4], "E"], [[4, 9], "N"]],
        output: [[[9, 4], "E"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no52$83b2o$83bo2bo$87bo9bobo$71bo15bo7bo3bo$68b4o15bo7bo$59bo7b4o12bo2b\no7bo4bo8b2o$58bobo6bo2bo12b2o10bo12b2o$57bo3b2o4b4o24bo3bo$43bo2b2o9bo\n3b2o5b4o14bobo8bobo$41b3o2b2o9bo3b2o8bo14b2o$40bo17bobo26bo$40b2o17bo\n31b2o9b2o$27b2o39bobo19bo2bo7bo2bo$28bo40b2o19b3o9b3o$28bobo38bo23b9o$\n29b2o49bo11bo2b5o2bo$37b2o39b2o12b2o2b3o2b2o$36bo2bo39b2o$37b2o$o75bo\n13bo2bo26bo2bo26bo$77b2o15bo29bo$o75b2o12bo3bo25bo3bo25bo$bo78b3o8b4o\n26b4o26bo$40b2o40bo$40bo30bo9bo$41b3o26bobo$43bo14b2o10b2obo8bobo$36b\n2obo18b2o10b2ob2o6bo2bo$27b2o3b2o2b2ob3o28b2obo6b2o10b2o$27bo2bo2bo8bo\n27bobo5b2o3bo8b2o$28b5o3b2ob3o29bo8b2o5b2o$37bobo41bo2bo4bo$30b2obo3bo\nbo42bobo$30bob2o4bo9$41b2o$39bo2bo42b2o$84bobo$38bo47bo2$39b2o$18b2o\n21bo14bo$18b2o36b3o$59bo$38b2o3b2o13b2o$38b2o3b2o$39b5o$40bobo2$40b3o\n2$18b3o49b2o$17bo3bo47bobo$16bo5bo48bo14b2o$16bo5bo63bobo$19bo18bo49bo\n$17bo3bo15bo50b2o$18b3o16b3o$19bo23bo$42b3o$41b5o$16b3o21b2o3b2o$16b3o\n9bobo37b2o15b2o$15bo3bo8bobo34bo3bo15bo$23bobo3bo34bobo2bobo11bobo$14b\n2o3b2o3b2o16b3o19bobo3b2o11b2o$24bo17b3o10b2o5b3ob2o9bo$54bobo4bo14bob\no$56bo5b3ob2o8bobo$43b2o19bob2o9bo$43b2o2$61b2o2b2o$61bo2bobo$62bobo$\n16b2o43b2ob2o13b2o$16b2o46bo14bo$64bobo13b3o$58b2o5b2o15bo$38bobo17bo$\n39b2o6b2o7bobo$39bo7bobo6b2o$42b2o4b3o$41bo2bo4b3o$43bo4b3o$39bo7bobo$\n38bob2o5b2o$38bo$37b2o!\n",
    },
    {
        name: "Not gate - E - E",
        input: [[[-1, 4], "E"]],
        output: [[[9, 4], "E"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no49$30bo$28b4o$19b2o5b4ob2o9b2o$17bo2bo3bo3b2ob3o8b2o40b2o$8b2o6bo7bo\n3b2ob2o49bo3bo$8b2o6bo6bo3b5o49bo5bo13b2o$16bo7b3o3bo42b2o5bo2bo3bo13b\n2o4b3o$17bo2bo50bo2bo12bo10b2o6b5o22bo$19b2o37bobo9bo7bo7bo10b3o5bo3bo\nbo19b3o$58bo3bo7bo6bo4bob2o12b2o6bo3b2o18bo$32bo29bo7bo7b2o9bobo9b2o\n27b2o$33b2o13b2o8bo4bo7bo2bo14b2o10b2o$32b2o14b2o12bo10b2o15bo$58bo3bo\n$58bobo8bobo21b2o9b2o$70b2o20bo2bo7bo2bo$70bo21b3o9b3o$83bo11b9o$39bob\no39b2o11bo2b5o2bo$40b2o40b2o10b2o2b3o2b2o$40bo$77bo$o77b2o10bo2bo26bo\n2bo$77b2o15bo29bo$o89bo3bo25bo3bo$bo45bo43b4o26b4o$48b2o31b3o$47b2o21b\no12bo$70b4o8bo$60b2o9b4o10b2o$60b2o9bo2bo9bobo$65bo5b4o8b3o4b2ob3o$65b\no4b4o8b3o4bo2b4o$54bobo13bo12b3o4b2o$55b2o27bobo$55bo29b2o5$62bo$63b2o\n$62b2o6$69bobo$70b2o$70bo5$77bo$78b2o$77b2o10$72b2o$73b2o$72bo$61b2o$\n60bo3bo28b2o$59bo5bo7bo19bobo$49b2o8bo3bob2o4bobo21bo$49b2o8bo5bo3b2o\n24b2o$60bo3bo4b2o12b2o$61b2o6b2o12b2o$71bobo$73bo!\n",
    },
    {
        name: "Half-adder - EE - ES",
        input: [[[-1, 4], "E"], [[-1, 14], "E"]],
        output: [[[19, 4], "E"], [[14, 19], "S"]],
        height: 10,
        width: 10,
        drawing: "",
        content: "\no23$101b2o$101b2o5$78b2o$78b2o2$100b3o$99bo3bo$79bo18bo5bo$78bobo17b2o\nbob2o$77bo3bo$78b3o$76b2o3b2o18bo$100bobo$100bobo$101b2o$103bo$77bo24b\n3o$77bo23bo3bo$77bob3o18bob3obo$96bo4b5o$82bo11b2o$79bob2o12b2o$79b2o\n3$74b2o3b2o7bo114b2o$74b2o3b2o7b2o113bo2bo$75b5o6bobobo116bo9bobo$76bo\nbo5b3o2b2o100bo15bo7bo3bo$188b4o15bo7bo$76b3o24b2o74bo7b4o12bo2bo7bo4b\no8b2o$103b2o73bobo6bo2bo12b2o10bo12b2o$177bo3b2o4b4o24bo3bo$163bo2b2o\n9bo3b2o5b4o14bobo8bobo$161b3o2b2o9bo3b2o8bo14b2o$95bo64bo17bobo26bo$\n76b2o15bobo64b2o17bo31b2o9b2o$76b2o16b2o51b2o39bobo19bo2bo7bo2bo$148bo\n40b2o19b3o9b3o$148bobo38bo23b9o$149b2o49bo11bo2b5o2bo$157b2o39b2o12b2o\n2b3o2b2o$156bo2bo39b2o$157b2o$o29bo2bo26bo2bo26bo2bo26bo2bo26bo2bo42bo\n13bo2bo26bo2bo26bo2bo26bo$34bo29bo29bo29bo29bo42b2o15bo29bo29bo$o29bo\n3bo25bo3bo25bo3bo25bo3bo25bo3bo41b2o12bo3bo25bo3bo25bo3bo25bo$bo29b4o\n26b4o26b4o26b4o26b4o45b3o8b4o26b4o26b4o26bo$160b2o40bo$160bo30bo9bo$\n110bo50b3o8bo17bobo$108bobo52bo9bo4b2o10b2obo8bobo$109b2o45b2obo11b3o\n4b2o10b2ob2o6bo2bo$147b2o3b2o2b2ob3o28b2obo6b2o10b2o$147bo2bo2bo8bo27b\nobo5b2o3bo8b2o32bo$148b5o3b2ob3o29bo8b2o5b2o37b3o$157bobo41bo2bo4bo39b\no$150b2obo3bobo42bobo43b2o$150bob2o4bo3$251bo$250b3o$250b3o2$125bo61bo\n60b2o3b2o$123bobo62bo59b2o3b2o$124b2o60b3o$205b2o$204bobo$206bo43b2o2$\n248b2o$248b2o3b2o$247bobo3bo$254b3o$256bo4$140bo61bo$138bobo62bo$139b\n2o60b3o$190b2o$189bobo$191bo2$233bo$233b2o$232bobo6$155bo61bo$153bobo\n62bo$154b2o60b3o19b2o$175b2o61bo$174bobo50bobo6bobo$176bo48bo3bo6b2o$\n225bo$224bo4bo$225bo$219b2o4bo3bo$218bobo6bobo$218bo$217b2o3$170bo$\n168bobo$169b2o$160b2o$159bobo$161bo10$104b2o79bo8bo$105bo77bobo6b3o18b\n2o$105bobo10bo65b2o5bo21b2o$106b2o9b4o24b2o44b2o$116b2obobo22bobo$115b\n3obo2bo23bo$116b2obob2o65b3o$117b4ob3o63b3o$109bobo6bo4bobo61bo3bo$\n110b2o13bo60bo5bo$110bo14b2o60bo3bo$188b3o19b2obob2o2$210bo5bo14b2o$\n231b2o$211b2ob2o$175bo37bo$173b2o$130b2o42b2o57b2o12b2o$129bobo54b2o\n59b2o$93b3o35bo55bo$95bo88b3o$94bo89bo31bo$124bobo83b3o4b2o10b2o3b2o$\n125b2o82bo3bo2b2o12b5o12b3o$125bo104b2ob2o12b3o$208bo5bo15b2ob2o11bo3b\no$154bo53b2o3b2o16b3o$154b3o88b2o3b2o$157bo$156b2o53bo11bobo$210bobo\n11b2o$163bo48bo11bo$115b2o47bo43bo36b3o$114bobo45b3o42bo12bo7bo20b2o$\n78b3o35bo89bo4bo8b2o6bobo3bo14b2o15bobo$80bo127bo10bobo6b2o3b3o14b2o\n14bo3bo$79bo125bo5bo20b5o11bobo5b2o12bo7bo$139bobo16b3o44bo5bo19bobobo\nbo10b2o6b2o8bo4bo4b4o$140b2o15bo3bo44bo3bo20b2o3b2o32bo4bobob2o9b2o$\n140bo15bo5bo44b3o56bo3bo3bo2bob3o8b2o$156bo5bo80b2o3b2o16bobo6bobob2o$\n159bo52b2o20bo8b2o3b2o26b4o$157bo3bo51b2o9bobo6bobo19bo22bo$158bo53bo\n14bo5bobo9b3o8b2o9bo$159bo2bo54b2o8bo6bo10b3o7b2o10bobo$162bo53bobo5bo\n2bo5b2o11bo20b2o$161bo16bo37bobob2o3b3o5b2o$100b2o60b3o14bo37bobobo11b\n2o$99bobo62bo12b3o39bo$63b3o35bo108bo8b2o$65bo143b3o7b3o38bo$64bo144b\n3o7b3o23b2o12bo$154bobo62b3o23b2o12b3o$155b2o50b2o3b2o5b2o$155bo51b2o\n3b2o5bo$217bobobo$216bobob2o$210bo5bobo$209bobo5b2o$30bo103b2o44bo27b\n2o$134b3o71b2o$30bo89bo15b2obo40bo12bo14b3o$85b2o31bobo4b3o8bo2bo5b2o\n34bo12bo14bobo$84bobo30bobo16b2obo5b2o45b3o15b2o$48b3o35bo24b2o3bo2bo\n7bo2b2o2b3o$50bo60b2o4bobo7bo3bo2b2o109bo$49bo68bobo6bo2bo113bo$120bo\n8b2o38bobo72b3o$30bo2bo26bo2bo86bo2bo16b2o8bo2bo26bo2bo$34bo29bo71b4o\n14bo15bo13bo29bo$30bo3bo25bo3bo70bo3bo10bo3bo25bo3bo25bo3bo$31b4o26b4o\n74bo11b4o26b4o26b4o$90b2o43bo2bo85bobo$90b2o135bo$125b2o100bo$126b2o\n17b2o7b2o68bo2bo$125bo19bo9bo30bo21bo16b3o$70b2o4bobo10b3o54b9o31b2o\n21bo$69bobo17b3o44b2o5b3o2b5o2b3o23b2o4b2o18b3o$33b3o35bo4b5o7bo3bo42b\n2o6bo2bo2b3o2bo2bo23b2o4b3o$35bo41b3o7bo5bo13bo9b2o18bo6b2o9b2o24b2o4b\n2o41bo$13b2o19bo43b2o8bo3bo13bobo7b4o58b2o6b2o7b2o15b2o15bo$13b2o40bob\no31b3o7b2o4bob2o5b3o2bo2bobo52bobo6bo8bobo14bobo14b3o$54bo2bo3b2o36b2o\n3b2ob2o9b2o2bo2bo25bo25bo19bo16bo$53b2o5b3ob2o2b2o35bob2o6bo9b2o17b2ob\no3b4o21b2o19b2o15b2o$13b3o29b2o4b2o3bo3bo3bo3bobo15bo19bobo5bo8bo3b2o\n9b2o2b2obobo4b4o5b2o$13b3o29b2o6b2o5bobo8bo13b2o20bo6bo10b2o10bobo2b2o\nbob2o3bo2bo5b2o$40b2o12bo2bo2b2o6bo2bo7b2o4bobo34bo2bo10b3o8b2o3b4o$\n25bo14b2o13bobo13bo7b2o41bobo10b3o8b2o3b4o$22b2o44bobo65b3o12bo$11b2o\n3b2o7bo42b2o67bobo$12b5o4bo4bo111b2o$13b3o6bob3o$14bo8b2o2bo12bo$18b3o\n3b3o3bo9bo47bo$20bo4b2o2b2o8bobo45b3o$19bo9bobo6b2ob2o43b5o$37bo5bo41b\nobobobo$40bo44b2o3b2o$37b2o3b2o2$88bo$15b3o18b3o48bobo$35b2obo48bobo$\n15bobo17b2o51bo$14b5o17b2o50b2o$13b2o3b2o17bobo48b2o$13b2o3b2o17bo2b2o\n46b2o$202b2o$201bobo$16bo184bo$17b2o181b2o2$19bo16b5o$35bob3obo$15bo2b\no17bo3bo$15b2o20b3o$38bo4$38b2o$38b2o!\n",
    },
    {
        name: "Half-adder - EE - EE",
        input: [[[-1, 4], "E"], [[-1, 14], "E"]],
        output: [[[19, 4], "E"], [[19, 14], "E"]],
        height: 10,
        width: 10,
        drawing: "",
        content: "\no23$101b2o$101b2o5$78b2o$78b2o2$100b3o$99bo3bo$79bo18bo5bo$78bobo17b2o\nbob2o$77bo3bo$78b3o$76b2o3b2o18bo$100bobo$100bobo$101b2o$103bo$77bo24b\n3o$77bo23bo3bo$77bob3o18bob3obo$96bo4b5o$82bo11b2o$79bob2o12b2o$79b2o\n3$74b2o3b2o7bo114b2o$74b2o3b2o7b2o113bo2bo$75b5o6bobobo116bo9bobo$76bo\nbo5b3o2b2o100bo15bo7bo3bo$188b4o15bo7bo$76b3o24b2o74bo7b4o12bo2bo7bo4b\no8b2o$103b2o73bobo6bo2bo12b2o10bo12b2o$177bo3b2o4b4o24bo3bo$163bo2b2o\n9bo3b2o5b4o14bobo8bobo$161b3o2b2o9bo3b2o8bo14b2o$95bo64bo17bobo26bo$\n76b2o15bobo64b2o17bo31b2o9b2o$76b2o16b2o51b2o39bobo19bo2bo7bo2bo$148bo\n40b2o19b3o9b3o$148bobo38bo23b9o$149b2o49bo11bo2b5o2bo$157b2o39b2o12b2o\n2b3o2b2o$156bo2bo39b2o$157b2o$o29bo2bo26bo2bo26bo2bo26bo2bo26bo2bo42bo\n13bo2bo26bo2bo26bo2bo26bo$34bo29bo29bo29bo29bo42b2o15bo29bo29bo$o29bo\n3bo25bo3bo25bo3bo25bo3bo25bo3bo41b2o12bo3bo25bo3bo25bo3bo25bo$bo29b4o\n26b4o26b4o26b4o26b4o45b3o8b4o26b4o26b4o26bo$160b2o40bo$160bo30bo9bo$\n110bo50b3o8bo17bobo$108bobo52bo9bo4b2o10b2obo8bobo$109b2o45b2obo11b3o\n4b2o10b2ob2o6bo2bo$147b2o3b2o2b2ob3o28b2obo6b2o10b2o$147bo2bo2bo8bo27b\nobo5b2o3bo8b2o32bo$148b5o3b2ob3o29bo8b2o5b2o37b3o$157bobo41bo2bo4bo39b\no$150b2obo3bobo42bobo43b2o$150bob2o4bo3$251bo$250b3o$250b3o2$125bo61bo\n60b2o3b2o$123bobo62bo59b2o3b2o$124b2o60b3o$205b2o$204bobo$206bo43b2o2$\n248b2o$248b2o3b2o$247bobo3bo$254b3o$256bo4$140bo61bo$138bobo62bo$139b\n2o60b3o$190b2o$189bobo$191bo2$233bo$233b2o$232bobo6$155bo61bo$153bobo\n62bo$154b2o60b3o19b2o$175b2o61bo$174bobo50bobo6bobo$176bo48bo3bo6b2o$\n225bo$224bo4bo$225bo$219b2o4bo3bo$218bobo6bobo$218bo$217b2o3$170bo$\n168bobo$169b2o$160b2o$159bobo$161bo10$104b2o79bo8bo$105bo77bobo6b3o$\n105bobo10bo65b2o5bo$106b2o9b4o24b2o44b2o$116b2obobo22bobo$115b3obo2bo\n23bo$116b2obob2o65b3o$117b4ob3o63b3o$109bobo6bo4bobo61bo3bo$110b2o13bo\n60bo5bo$110bo14b2o60bo3bo$188b3o5$175bo$173b2o$130b2o42b2o$129bobo54b\n2o$93b3o35bo55bo$95bo88b3o$94bo89bo$124bobo$125b2o$125bo2$154bo$154b3o\n$157bo$156b2o2$163bo$115b2o47bo$114bobo45b3o$78b3o35bo$80bo$79bo$139bo\nbo16b3o$140b2o15bo3bo$140bo15bo5bo$156bo5bo$159bo$157bo3bo$158bo$159bo\n2bo$162bo$161bo16bo$100b2o60b3o14bo$99bobo62bo12b3o$63b3o35bo$65bo$64b\no$154bobo$155b2o$155bo5$30bo103b2o44bo$134b3o$30bo89bo15b2obo40bo12bo$\n85b2o31bobo4b3o8bo2bo5b2o34bo12bo$84bobo30bobo16b2obo5b2o45b3o$48b3o\n35bo24b2o3bo2bo7bo2b2o2b3o$50bo60b2o4bobo7bo3bo2b2o$49bo68bobo6bo2bo$\n120bo8b2o38bobo$30bo2bo26bo2bo86bo2bo16b2o8bo2bo26bo2bo$34bo29bo71b4o\n14bo15bo13bo29bo$30bo3bo25bo3bo70bo3bo10bo3bo25bo3bo25bo3bo$31b4o26b4o\n74bo11b4o26b4o26b4o$90b2o43bo2bo$90b2o$125b2o$126b2o17b2o7b2o$125bo19b\no9bo30bo21bo$70b2o4bobo10b3o54b9o31b2o21bo$69bobo17b3o44b2o5b3o2b5o2b\n3o23b2o4b2o18b3o$33b3o35bo4b5o7bo3bo42b2o6bo2bo2b3o2bo2bo23b2o4b3o$35b\no41b3o7bo5bo13bo9b2o18bo6b2o9b2o24b2o4b2o$13b2o19bo43b2o8bo3bo13bobo7b\n4o58b2o6b2o7b2o15b2o$13b2o40bobo31b3o7b2o4bob2o5b3o2bo2bobo52bobo6bo8b\nobo14bobo$54bo2bo3b2o36b2o3b2ob2o9b2o2bo2bo25bo25bo19bo16bo$53b2o5b3ob\n2o2b2o35bob2o6bo9b2o17b2obo3b4o21b2o19b2o15b2o$13b3o29b2o4b2o3bo3bo3bo\n3bobo15bo19bobo5bo8bo3b2o9b2o2b2obobo4b4o5b2o$13b3o29b2o6b2o5bobo8bo\n13b2o20bo6bo10b2o10bobo2b2obob2o3bo2bo5b2o$40b2o12bo2bo2b2o6bo2bo7b2o\n4bobo34bo2bo10b3o8b2o3b4o$25bo14b2o13bobo13bo7b2o41bobo10b3o8b2o3b4o$\n22b2o44bobo65b3o12bo$11b2o3b2o7bo42b2o67bobo$12b5o4bo4bo111b2o$13b3o6b\nob3o$14bo8b2o2bo12bo$18b3o3b3o3bo9bo47bo$20bo4b2o2b2o8bobo45b3o$19bo9b\nobo6b2ob2o43b5o$37bo5bo41bobobobo$40bo44b2o3b2o$37b2o3b2o2$88bo$15b3o\n18b3o48bobo$35b2obo48bobo$15bobo17b2o51bo$14b5o17b2o50b2o$13b2o3b2o17b\nobo48b2o$13b2o3b2o17bo2b2o46b2o$202b2o$201bobo$16bo184bo$17b2o181b2o2$\n19bo16b5o$35bob3obo$15bo2bo17bo3bo$15b2o20b3o$38bo4$38b2o$38b2o!\n",
    },
    {
        name: "Turn clockwise faster",
        input: [[[-1, 4], "E"]],
        output: [[[4, 9], "S"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no2$88b2o$88b2o6$54b2o$54b2o4$70b2o14b2o3b2o$31b2o37b2o16b3o$31b2o54bo\n3bo$88bobo$89bo2$53b3o$32bo19bo3bo$32bo18bo5bo$31bobo18bo3bo33b3o$30b\n2ob2o18b3o28bobo$29bo5bo17b3o11b2o3b2o10b2o4bobo$32bo52bo3b5o$29b2o3b\n2o32bo3bo15b2o3b2o$69b3o16b2o3b2o$69b3o$30b4o21b3o$30bo2b2o15bo3b2ob2o\n19bo$31bob2o13b2o4b2ob2o17b2o12b2o$49b2o3b5o18b2o$32b2o19b2o3b2o$33bo\n34bo5bo6b2o$67b3o5bo4b2o$67b3o3b3o6bo$27b2obob2o$27bo5bo5bo14b2o9b2o3b\n2o19b2obob2o$28bo3bo7bo24b2o3b2o19bo5bo$29b3o6b3o51bo3bo$89bo3b3o$56b\n2o10bo19b2o$56b2o9bobo18bobo$66b2o6bobo$66b2o9bo6b2o$66b3o8bo6bobo$67b\nobo4bo2bo3b2obobo$29b2o37b2o5b3o3bobobo$29b2o52bo8bo$83b2o7bo$83b3o5bo\nbo$83b3o4b2ob2o$54bo28b3o3bo5bo$55bo27b2o7bo$53b3o27bo5b2o3b2o$81bobob\no$81b2obobo$84bobo6bo$84b2o7bo$94bo3$91b2o$91b2o4$69bo$70bo$o2bo64b3o$\n4bo$o3bo$b4o6$89bo$87b3o$86bo$86b2o7$84bo$83b3o$82b5o$81b2o3b2o3$83bo$\n83bo2$86b2o$86bo$87b3o$89bo!\n",
    },
    {
        name: "Turn clockwise normal",
        input: [[[-1, 4], "E"]],
        output: [[[4, 9], "S"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no3$63b2o$63b2o9$60b2obob2o2$60bo5bo14b2o$81b2o$61b2ob2o$63bo2$83b2o12b\n2o$97b2o3$66bo$60b3o4b2o10b2o3b2o$59bo3bo2b2o12b5o12b3o$80b2ob2o12b3o$\n58bo5bo15b2ob2o11bo3bo$58b2o3b2o16b3o$95b2o3b2o2$61bo11bobo$60bobo11b\n2o$62bo11bo$58bo36b3o$57bo12bo7bo20b2o$56bo4bo8b2o6bobo3bo14b2o15bobo$\n58bo10bobo6b2o3b3o14b2o14bo3bo$55bo5bo20b5o11bobo5b2o12bo7bo$55bo5bo\n19bobobobo10b2o6b2o8bo4bo4b4o$56bo3bo20b2o3b2o32bo4bobob2o9b2o$57b3o\n56bo3bo3bo2bob3o8b2o$93b2o3b2o16bobo6bobob2o$62b2o20bo8b2o3b2o26b4o$\n63b2o9bobo6bobo19bo22bo$62bo14bo5bobo9b3o8b2o9bo$67b2o8bo6bo10b3o7b2o\n10bobo$66bobo5bo2bo5b2o11bo20b2o$66bobob2o3b3o5b2o$67bobobo11b2o$69bo$\n60bo8b2o$59b3o7b3o38bo$59b3o7b3o23b2o12bo$69b3o23b2o12b3o$57b2o3b2o5b\n2o$57b2o3b2o5bo$67bobobo$66bobob2o$60bo5bobo$59bobo5b2o$58b2o$58b2o$\n58b3o$59bobo$60b2o2$95bo$94bo$94b3o$o2$o$bo$74bobo$77bo$77bo$74bo2bo$\n75b3o4$80bo$79bo$79b3o26$52b2o$51bobo$51bo$50b2o!\n",
    },
    {
        name: "Turn clockwise slower",
        input: [[[-1, 4], "E"]],
        output: [[[4, 9], "S"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no2$88b2o$88b2o11$70b2o14b2o3b2o$70b2o16b3o$87bo3bo22b2o$88bobo23b2o$\n89bo4$137b2o$90b3o21b3o20b2o$84bobo$67b2o3b2o10b2o4bobo21bobo$85bo3b5o\n19b5o19bo$68bo3bo15b2o3b2o17b2o3b2o17b3o$69b3o16b2o3b2o17b2o3b2o16bo3b\no$69b3o65bo$134bo5bo$78bo35b2o18bo5bo$76b2o12b2o21b2ob2o17bo3bo$77b2o\n35bo2bo18b3o$114bo$68bo5bo6b2o34bo$67b3o5bo4b2o33b2o$67b3o3b3o6bo$135b\no$65b2o3b2o19b2obob2o12b2o3b2o$65b2o3b2o19bo5bo13b5o5bo$92bo3bo15b3o7b\n2o11bo$89bo3b3o17bo7b2o12bobo$68bo19b2o45b2o$67bobo18bobo$66b2o6bobo$\n66b2o9bo6b2o$66b3o8bo6bobo49b2o3b2o$67bobo4bo2bo3b2obobo41bo$68b2o5b3o\n3bobobo41bo9bo3bo$83bo8bo19b2o13b3o8b3o$83b2o7bo19b2o24b3o$83b3o5bobo$\n83b3o4b2ob2o$83b3o3bo5bo$83b2o7bo$83bo5b2o3b2o43b2o$81bobobo53b2o$81b\n2obobo$84bobo6bo$84b2o7bo$94bo2$113bo$91b2o19bo$91b2o19b3o6$o2bo$4bo$o\n3bo$b4o$74bobo$77bo$77bo$74bo2bo20bo$75b3o19bo$97b3o13$83bo$82bo$82b3o\n10$74bobo$77bo$77bo$59bo8bo5bo2bo$59b3o5bo7b3o$62bo4b3o$61b2o2$64bo$\n63b3o$62bo3bo$64bo$61bo5bo$61bo5bo$62bo3bo$63b3o7$61b2o$62bo$59b3o$59b\no!\n",
    },
    {
        name: "Turn anti-clockwise",
        input: [[[-1, 4], "E"]],
        output: [[[4, -1], "N"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no36$47b2o$48bo$48bobo$49b2o29$80b2o$80bobo$72b3o5bo$o71bo2bo$72bo$o71b\no$bo71bobo9$95b2o$57b2o36bobo$57b2o36bo3$55bo$56bo7b2o$56bo6bobo$63bob\nob2o$64bobobo$54b2o3b2o5bo$57bo7b2o$54bo5bo3b3o25b2o$55b2ob2o4b3o25bo\n2bo$56bobo5b3o$57bo7b2o29bo13b2o$57bo8bo43bobo$64bobobo3b3o5b2o12b2o\n14bo$63bobob2o3bo2bo4bobo10bo$63bobo6bo8b3o$64b2o6bo9b2o$73bobo6b2o6b\n2o3b2o$59bobo18bobo7b2o3b2o32b2o$60b2o19bo9b5o3bo17b3o2bo5bo3bo$54b3o\n3bo31bobo4b2o12bo3bo9bo5bo$53bo3bo40bobo10bobo4bo8bo3bob2o2b2o$52bo5bo\n19b2o3b2o7b3o14b2o16bo5bo3b2o$52b2obob2o19b2o3b2o18b2o4b2o17bo3bo$103b\n2o4b2o18b2o$67bo6b3o3b3o28bobo$68b2o4bo5b3o30bo$67b2o6bo5bo13bo$94bobo\n$71b2o20bo3bo$58b2o12b2o20b3o$71bo20b2o3b2o2$78b3o$55b2o3b2o16b3o$55b\n2o3b2o15bo3bo$56b5o3bo$57bobo4b2o10b2o3b2o$63bobo$57b3o3$94b2o$94b2o$\n60bo$59bobo$58bo3bo$59b3o16b2o$57b2o3b2o14b2o11$60b2o$60b2o!\n",
    },
    {
        name: "Duplicate clockwise",
        input: [[[-1, 4], "E"]],
        output: [[[9, 4], "E"], [[4, 9], "S"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no2$88b2o$88b2o8$30b2o$30b2o2$70b2o14b2o3b2o$70b2o16b3o$32b2o53bo3bo$\n88bobo$89bo3$28b2o3b2o$29b5o$29b2ob2o56b3o$29b2ob2o50bobo$30b3o34b2o3b\n2o10b2o4bobo$85bo3b5o$68bo3bo15b2o3b2o$69b3o16b2o3b2o$69b3o2$78bo$35bo\n40b2o12b2o$29bo3bobo41b2o$28b3o3b2o$27b5o36bo5bo6b2o$26bobobobo34b3o5b\no4b2o$26b2o3b2o34b3o3b3o6bo$40b3o$40bo24b2o3b2o19b2obob2o$29bo11bo23b\n2o3b2o19bo5bo$28bobo7b4o50bo3bo$28bobo7bo2bo47bo3b3o$29bo10b2o26bo19b\n2o$28b2o37bobo18bobo$28b2o36b2o6bobo$28b2o36b2o9bo6b2o$33b2o15bo15b3o\n8bo6bobo$34b2o12bobo16bobo4bo2bo3b2obobo$33bo15b2o17b2o5b3o3bobobo$83b\no8bo$20b2o61b2o7bo$18bo2bo61b3o5bobo$17bo7b3o3bo51b3o4b2ob2o$9b2o6bo6b\no3b5o50b3o3bo5bo$9b2o6bo7bo3b2ob2o49b2o7bo$18bo2bo3bo3b2ob3o8b2o38bo5b\n2o3b2o$20b2o5b4ob2o9b2o36bobobo$29b4o48b2obobo$31bo52bobo6bo$84b2o7bo$\n94bo$65bo$63bobo$64b2o25b2o$91b2o6$o2$o$bo22$97b2o$97bo$98b3o$100bo!\n",
    },
    {
        name: "Duplicate anti-clockwise",
        input: [[[-1, 4], "E"]],
        output: [[[9, 4], "E"], [[4, -1], "N"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no18$97b2o$97b2o8$97b3o$90bo5bo3bo$89b2o4bo5bo$89bobo3b2obob2o3$98bo$\n97bobo$97bobo$98b3o$100b2o$100bo$101b3o$72b3o28bo$72bo2bo$72bo$72bo$\n73bobo$86b3o$88bo$87bo13$71b3o$73bo$72bo8$72b3o$o71bo2bo$72bo$o71bo$bo\n71bobo$56b3o$58bo$57bo2$24bo$23bobo$13b2o7bob2o10b2o$12bobo6b2ob2o10b\n2o$2b2o7bo6b3obob2o$2b2o7bo2bo2bo2bo2bobo$11bo6b2o4bo63b2o$12bobo73b2o\n$13b2o2$25bobo$26b2o13b3o37b2o$26bo16bo37bobo$21b2o19bo35b2obobo$21b2o\n55bobobo$80bo$33b2o44b2o5b2obob2o$21b3o8bobo43b3o$21b3o7b3o44b3o5bo5bo\n$78b3o$33b2o44b2o6b2ob2o$34bo37b3o5bo8bo$19b2o3b2o8bo30b2o5bo2bo2bobob\no$20b5o40b2o5bo5b2obobo$21b3o48bo8bobo$22bo50bobo5b2o$26b3o34bo$28bo\n35bo21bo$27bo36bo19b2o4b3o$85b2o2bo3bo2$62b2o3b2o19bo5bo$65bo22b2o3b2o\n$62bo5bo2b2o$23b3o37b2ob2o2bobo$64bobo5bo4bobo$23bobo39bo11b2o$22b5o\n38bo8bo3bo$21b2o3b2o45b2o$21b2o3b2o45bobo2$67bo$24bo41b3o$25b2o38bo3bo\n$64bob3obo14b2o3b2o$27bo37b5o11b2o3b5o$80b2o4b2ob2o$23bo2bo55bo3b2ob2o\n$23b2o62b3o5$85b3o$85b3o$84bo3bo$67b2o14bo5bo$67b2o15bo3bo$85b3o10$85b\n2o$85b2o!\n",
    },
    {
        name: "Wire - E - E",
        input: [[[-1, 4], "E"]],
        output: [[[9, 4], "E"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "!",
    },
    {
        name: "Slow wire - E - E",
        input: [[[-1, 4], "E"]],
        output: [[[9, 4], "E"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no12$124b2o$124b2o5$101b2o$101b2o3$123b3o$122bo3bo$102bo18bo5bo$100b2ob\n2o16bo5bo$124bo$99bo5bo16bo3bo$123b3o$99b2obob2o18bo3$100bo24b3o$100bo\n2bo21b3o$100bo23bo3bo$103b2o13bobo$104bo13b2o3b2o3b2o$102bobo14bo$102b\n2o3$97b2o3b2o$97bo5bo$110bo$98bo3bo5bobo$99b3o7b2o$126b2o$126b2o5$70bo\n28b2o$69bobo27b2o$67b2o3bo14b2o$59b2o6b2o3bo13bobo$58bobo6b2o3bo12b3o\n4b2o$43bobo11bo6b2o3bobo12b3o4bo2b4o$38bo4bo2bo10bo2bo2bo2bo3bo6bo7b3o\n4b2ob3o27bo$39b2o5b2o9bo6b2o9b2o9bobo34bobo$23bo10b2o8bo3b2o8bobo15b2o\n9b2o35b2o$21b3o10b2o10b2o11b2o$20bo22bo2bo8bo$20b2o21bobo10b2o21b2o9b\n2o$7b2o46b2o21bo2bo7bo2bo$8bo69b3o9b3o$8bobo57bobo10b9o$9b2o57b2o10bo\n2b5o2bo$17bo51bo10b2o2b3o2b2o$17b2o$18bo43bobo$o62b2o25bo2bo26bo2bo26b\no$63bo12b4o14bo29bo$o12bo61bo3bo10bo3bo25bo3bo9b2o14bo$bo10bobo64bo11b\n4o26b4o9b2o15bo$15bo4b2o45b2o6bo2bo55bo$12bo2bo4bo34b2o9bobo$13b3o5b3o\n31b3o10bo$23bo22b2o9b2obo11bo$16b2obo26bo5bo4bo2bo10b2o$7b2o3b2o2b2ob\n3o29bo5b2obo9b2o4b2o2b2o48b2o$7bo2bo2bo8bo24bo3bo3b3o11b3o4b2o2b2o47bo\nbo$8b5o3b2ob3o27bo5b2o13b2o4b2o53bo$17bobo51b2o$10b2obo3bobo52bo$10bob\n2o4bo3$122b3o$124bo$123bo5$115b2o$114bobo$116bo6$107b3o$109bo$108bo5$\n100b2o$99bobo$101bo6$92b3o$94bo$93bo5$85b2o$84bobo$86bo6$77b3o$79bo$\n68bo9bo$67bobo$67b2obo8bobo$55b2o10b2ob2o6bo2bo4bo$55b2o10b2obo6b2o5b\n2o$67bobo5b2o3bo8b2o$68bo8b2o10b2o$78bo2bo$79bobo!\n",
    },
    {
        name: "Slower wire - E - E",
        input: [[[-1, 4], "E"]],
        output: [[[39, 4], "E"]],
        height: 5,
        width: 20,
        drawing: "",
        content: "\no5$87bo49bo49bo49bo49bo49bo49bo49bo49bo49bo$87b3o47b3o9bo37b3o47b3o47b\n3o9bo37b3o47b3o47b3o9bo37b3o47b3o$90bo7b2o40bo8bo40bo7b3o39bo7b2o40bo\n8bo40bo7b3o39bo7b2o40bo8bo40bo7b3o39bo7b2o$89bo9b2obo36b2o7bob2obo35b\n2o11bo36bo9b2obo36b2o7bob2obo35b2o11bo36bo9b2obo36b2o7bob2obo35b2o11bo\n36bo9b2obo$89bo3bo5b6o48bo45bo2bobo34bo3bo5b6o48bo45bo2bobo34bo3bo5b6o\n48bo45bo2bobo34bo3bo5b6o$93bo10bo39bo5bo3bo88bo10bo39bo5bo3bo88bo10bo\n39bo5bo3bo88bo10bo$95bo3b3ob3o37bobo4bo2b2o45b4obo39bo3b3ob3o37bobo4bo\n2b2o45b4obo39bo3b3ob3o37bobo4bo2b2o45b4obo39bo3b3ob3o$89bo5bo5bo3bo37b\no2bo3bo4bo37b2ob2o3b3o2bo32bo5bo5bo3bo37bo2bo3bo4bo37b2ob2o3b3o2bo32bo\n5bo5bo3bo37bo2bo3bo4bo37b2ob2o3b3o2bo32bo5bo5bo3bo$90bo4bo8b2o38b2o6bo\nb2o37bo2bo7bo35bo4bo8b2o38b2o6bob2o37bo2bo7bo35bo4bo8b2o38b2o6bob2o37b\no2bo7bo35bo4bo8b2o$92bo12b2o87b2o8bo2bo34bo12b2o87b2o8bo2bo34bo12b2o\n87b2o8bo2bo34bo12b2o$106b2o48b2o49bo48b2o48b2o49bo48b2o48b2o49bo48b2o$\n106bo49bo49bo49bo49bo49bo49bo49bo49bo49bo$98bo8b3o47b3o47b3o38bo8b3o\n47b3o47b3o38bo8b3o47b3o47b3o38bo8b3o$96bobo10bo29b2o18bo49bo36bobo10bo\n29b2o18bo49bo36bobo10bo29b2o18bo49bo36bobo10bo$97b2o41b2o105b2o41b2o\n105b2o41b2o105b2o$115b2o22bo25b2o48b2o48b2o22bo25b2o48b2o48b2o22bo25b\n2o48b2o48b2o$115bo49bo49bo49bo49bo49bo49bo49bo49bo49bo$113bobo37bo9bob\no47bobo47bobo37bo9bobo47bobo47bobo37bo9bobo47bobo47bobo$84b2o27b2o36bo\nbo9b2o48b2o19b2o27b2o36bobo9b2o48b2o19b2o27b2o36bobo9b2o48b2o19b2o27b\n2o$85b2o65b2o81b2o65b2o81b2o65b2o81b2o$84bo149bo149bo149bo$159b2o47b2o\n99b2o47b2o99b2o47b2o$109b3o46bo2bo45bobo49b3o46bo2bo45bobo49b3o46bo2bo\n45bobo49b3o$109bo48bobo18b2o26bobo49bo48bobo18b2o26bobo49bo48bobo18b2o\n26bobo49bo$109bo49bo20b2o26b2o49bo49bo20b2o26b2o49bo49bo20b2o26b2o49bo\n$102bobo74bo28b2o42bobo74bo28b2o42bobo74bo28b2o42bobo$102b2o10bo49bo\n48bo38b2o10bo49bo48bo38b2o10bo49bo48bo38b2o10bo$103bo8bobo45bob3o49b2o\n37bo8bobo45bob3o49b2o37bo8bobo45bob3o49b2o37bo8bobo$110bo3bo9b2o34bob\n2o45b3obo46bo3bo9b2o34bob2o45b3obo46bo3bo9b2o34bob2o45b3obo46bo3bo$\n109b2o14b2o32b2obo50bo45b2o14b2o32b2obo50bo45b2o14b2o32b2obo50bo45b2o$\n109b2ob2o10bo22bobo12b2o44bo50b2ob2o10bo22bobo12b2o44bo50b2ob2o10bo22b\nobo12b2o44bo50b2ob2o$109b2o36b2o11bobo47bob2o45b2o36b2o11bobo47bob2o\n45b2o36b2o11bobo47bob2o45b2o$107b2o3bo35bo9bob3o45bob2o45b2o3bo35bo9bo\nb3o45bob2o45b2o3bo35bo9bob3o45bob2o45b2o3bo$69b2o39bo46b4o47b2o9b2o39b\no46b4o47b2o9b2o39bo46b4o47b2o9b2o39bo$70b2o33bo3bo45b3o47b2o13b2o33bo\n3bo45b3o47b2o13b2o33bo3bo45b3o47b2o13b2o33bo3bo$69bo34bob2o46bobo35bob\no9bobo12bo34bob2o46bobo35bobo9bobo12bo34bob2o46bobo35bobo9bobo12bo34bo\nb2o$104bo49bo37b2o10bo49bo49bo37b2o10bo49bo49bo37b2o10bo49bo$103b2o48b\n2o38bo9b2o48b2o48b2o38bo9b2o48b2o48b2o38bo9b2o48b2o$164b2o148b2o148b2o\n$165b2o148b2o148b2o$87bobo74bo72bobo74bo72bobo74bo72bobo$87b2o148b2o\n148b2o148b2o$88bo149bo149bo149bo$109b2o148b2o148b2o$110b2o148b2o148b2o\n$109bo22bobo124bo22bobo124bo22bobo$132b2o148b2o148b2o$133bo149bo149bo\n136bobo$54b2o148b2o148b2o148b2o63bo2bo$55b2o148b2o148b2o148b2o61b2o10b\no6bo$54bo122bobo24bo122bobo24bo122bobo24bo53bo7b2o3bo8bo5bobo$177b2o\n148b2o148b2o79bobo7b2o9bo6b2obo$178bo149bo149bo62bo17bobo7bo2bo2b2o9b\n2ob2o3b2o$149b2o148b2o148b2o64bo25b2o16bo2bo7bobo2bo2b3o5b2obo4b2o$\n150b2o148b2o148b2o63b3o18b2o4b2o15bobo13b4o7bobo$23bo2b2o44bobo74bo72b\nobo74bo72bobo74bo68bo3bobo7b2o2b2o4b3o13bobo15b2o9bo$21b3o2b2o44b2o\n148b2o148b2o143b2o3b2o8b2o2b2o4b2o7bobo4bo$20bo52bo149bo149bo148b2o17b\n2o9b2o$20b2o72b2o148b2o148b2o145bo10bo24b2o9b2o$7b2o86b2o148b2o148b2o\n123b2o47bo6bo2bo7bo2bo$8bo85bo22bobo124bo22bobo124bo22bobo147b2o7b3o9b\n3o$8bobo106b2o148b2o148b2o149b2o9b9o$9b2o107bo149bo149bo159bo2b5o2bo$\n17bo21b2o148b2o148b2o148b2o26b2o3b2o35bo18b2o2b3o2b2o$17b2o21b2o148b2o\n148b2o148b2o25b2o3b2o36b2o$18bo20bo122bobo24bo122bobo24bo122bobo24bo\n69b2o$o2bo158b2o148b2o148b2o55b3o48bo2bo$4bo22bo135bo149bo149bo55b3o\n52bo$o3bo8bo14bo105b2o148b2o148b2o84bo49bo3bo$b4o7bobo11b3o17bo88b2o\n148b2o148b2o134b4o$15bo4b2o22b3o10bobo74bo72bobo74bo72bobo74bo$12bo2bo\n4bo22bo13b2o148b2o148b2o193b2o$13b3o5b3o19b2o13bo149bo149bo158b2o31bo\n3bo5bo2b3o$23bo18b2o35b2o148b2o148b2o137bo25b2o3bo5bo9bo3bo$16b2obo11b\n2o8b2o37b2o148b2o148b2o133b3o26b2o2b2obo3bo8bo4bobo$7b2o3b2o2b2ob3o8bo\n2bo4bo3bo36bo22bobo124bo22bobo124bo22bobo110bo33bo5bo16b2o4b2o$7bo2bo\n2bo8bo7bobo3b3ob3o59b2o148b2o148b2o146bo3bo17b2o4b2o$8b5o3b2ob3o9bo9bo\n61bo149bo149bo148b2o18b2o$17bobo16b6o132b2o148b2o148b2o93bobo11b2o$10b\n2obo3bobo6b2o8b2obo135b2o148b2o148b2o92bo12bobo$10bob2o4bo8bo7b2o110bo\nbo24bo122bobo24bo122bobo24bo109bo$24b3o120b2o148b2o148b2o$24bo123bo\n149bo149bo$119b2o148b2o148b2o$120b2o148b2o148b2o$42bobo74bo72bobo74bo\n72bobo74bo$42b2o148b2o148b2o$43bo149bo149bo$64b2o148b2o148b2o184bo$65b\n2o148b2o148b2o184bo$64bo22bobo124bo22bobo124bo22bobo159b3o$87b2o148b2o\n148b2o$88bo149bo149bo$159b2o148b2o148b2o$160b2o148b2o148b2o$132bobo24b\no122bobo24bo122bobo24bo$132b2o148b2o148b2o$133bo149bo149bo145b2o$104b\n2o148b2o148b2o172bo2bo$105b2o148b2o148b2o171bo$27bobo74bo72bobo74bo72b\nobo74bo173bo$27b2o148b2o148b2o231b3o3bo11bobo$28bo149bo149bo233bo2b2o\n11bobo$9b2o38b2o8b2o48b2o48b2o38b2o8b2o48b2o48b2o38b2o8b2o48b2o150bo3b\nobo11bo$10bo39b2o8bo49bo49bo39b2o8bo49bo49bo39b2o8bo49bo$10bob2o2bo32b\no10bobo9bobo35bobo47bob2o2bo32bo10bobo9bobo35bobo47bob2o2bo32bo10bobo\n9bobo35bobo$11bo5bo43b2o9b2o37b2o48bo5bo43b2o9b2o37b2o48bo5bo43b2o9b2o\n37b2o163b2o3b2o$73bo149bo149bo168bo8bo2bo21bo5bo$18bo125b2o22bo125b2o\n22bo125b2o95bobo10bo$13b2o50b2o49b2o27b2o16b2o50b2o49b2o27b2o16b2o50b\n2o49b2o27b2o92b2o3bo5b2o3bo2bo14b2o2bo3bo$64bo2bo48bobo25bo69bo2bo48bo\nbo25bo69bo2bo48bobo25bo89b2o3b2o3bo4bobob2o3b4o10b2o4b3o$15b3o47bobo\n50bo46b3o47bobo50bo46b3o47bobo50bo115b2o3b2o3bo14b4o11bo$22bo43bo49b2o\n54bo43bo49b2o54bo43bo49b2o123bobo5b2o8bo2bo5b2o$23bo65b2o25bo56bo65b2o\n25bo56bo65b2o25bo125bo16b4o5b2o$11bo9b3o38bo27b2o19bo49bo9b3o38bo27b2o\n19bo49bo9b3o38bo27b2o19bo146b4o$11b3obo44b2o27bo21bobo47b3obo44b2o27bo\n21bobo47b3obo44b2o27bo21bobo144bo$12b2obo46bob3o44bo3bo46b2obo46bob3o\n44bo3bo46b2obo46bob3o44bo3bo$13bob2o45bo14bo37b2o46bob2o45bo14bo37b2o\n46bob2o45bo14bo37b2o160bo$12b2o20b2o31bo10bo33b2ob2o45b2o20b2o31bo10bo\n33b2ob2o45b2o20b2o31bo10bo33b2ob2o158b2ob2o$13bobo19b2o9bo15b2obo10b3o\n17bo18b2o29bo16bobo19b2o9bo15b2obo10b3o17bo18b2o29bo16bobo19b2o9bo15b\n2obo10b3o17bo18b2o29bo$13b3obo16bo9b3o17b2obo26b3o16bo3b2o25b3o16b3obo\n16bo9b3o17b2obo26b3o16bo3b2o25b3o16b3obo16bo9b3o17b2obo26b3o16bo3b2o\n25b3o127bo5bo$15b4o24bo22b2o25bo21bo27bo21b4o24bo22b2o25bo21bo27bo21b\n4o24bo22b2o25bo21bo27bo$18b3o23bo24b2o22b2o21bo3bo22b2o23b3o23bo24b2o\n22b2o21bo3bo22b2o23b3o23bo24b2o22b2o21bo3bo22b2o129b2obob2o$19bobo19bo\n2bo24bobo20b2o24b2obo9b2o36bobo19bo2bo24bobo20b2o24b2obo9b2o36bobo19bo\n2bo24bobo20b2o24b2obo9b2o$21bo19bo29bo9b2o8b2o28bo8bo2b2o4bob2o28bo19b\no29bo9b2o8b2o28bo8bo2b2o4bob2o28bo19bo29bo9b2o8b2o28bo8bo2b2o4bob2o$\n21b2o8b3o4b3o2bo27b2o7bo2bo4bo3bo28b2o7b5o2bo4bo28b2o8b3o4b3o2bo27b2o\n7bo2bo4bo3bo28b2o7b5o2bo4bo28b2o8b3o4b3o2bo27b2o7bo2bo4bo3bo28b2o7b5o\n2bo4bo$31bo5b4obo37bobo3b3ob3o44bo2b2o39bo5b4obo37bobo3b3ob3o44bo2b2o\n39bo5b4obo37bobo3b3ob3o44bo2b2o$31bo49bo9bo45bo3bo39bo49bo9bo45bo3bo\n39bo49bo9bo45bo3bo$36bo2bobo44b6o48bo45bo2bobo44b6o48bo45bo2bobo44b6o\n48bo$26b2o11bo36b2o8b2obo36b2o7bob2obo35b2o11bo36b2o8b2obo36b2o7bob2ob\no35b2o11bo36b2o8b2obo36b2o7bob2obo$27bo7b3o39bo7b2o40bo8bo40bo7b3o39bo\n7b2o40bo8bo40bo7b3o39bo7b2o40bo8bo$24b3o47b3o47b3o9bo37b3o47b3o47b3o9b\no37b3o47b3o47b3o9bo140b2o$24bo49bo49bo49bo49bo49bo49bo49bo49bo152b2o!\n",
    },
    {
        name: "Cross - EN - EN",
        input: [[[-1, 4], "E"], [[4, 9], "N"]],
        output: [[[9, 4], "E"], [[4, -1], "N"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "!",
    },
    {
        name: "Cross - ES - ES",
        input: [[[-1, 4], "E"], [[4, -1], "S"]],
        output: [[[9, 4], "E"], [[4, 9], "S"]],
        height: 5,
        width: 5,
        drawing: "",
        content: "!",
    },
    {
        name: "Terminator - E",
        input: [[[-1, 4], "E"]],
        output: [],
        height: 5,
        width: 5,
        drawing: "",
        content: "\no68$12b2o$12bo$10bobo$o2bo6b2o$4bo$o3bo$b4o!\n",
    },
];
var False = { type: 'False' };
var True = { type: 'True' };
function evalBExp(x, env) {
    switch (x.type) {
        case 'False':
            return false;
        case 'True':
            return true;
        case 'Not':
            return !(evalBExp(x.op, env));
        case 'And':
            return (evalBExp(x.op1, env) && evalBExp(x.op2, env));
        case 'Or':
            return (evalBExp(x.op1, env) || evalBExp(x.op2, env));
        case 'Var':
            var v_1 = x.name;
            var g_1 = x.generation;
            var val = env.filter(function (elem) { return elem.name == v_1 && elem.generation == g_1; });
            return val[0].value;
    }
}
function stringOfBExp(x, parent) {
    if (parent === void 0) { parent = ""; }
    switch (x.type) {
        case 'False':
            return "false";
        case 'True':
            return "true";
        case 'Not':
            return "¬ " + stringOfBExp(x.op, x.type);
        case 'And':
            var s1 = stringOfBExp(x.op1, x.type);
            var s2 = stringOfBExp(x.op2, x.type);
            var and_res = s1 + " ∧ " + s2;
            if (parent == '' || parent == x.type) {
                return and_res;
            }
            return "(" + and_res + ")";
        case 'Or':
            var t1 = stringOfBExp(x.op1, x.type);
            var t2 = stringOfBExp(x.op2, x.type);
            var or_res = t1 + " ∨ " + t2;
            if (parent == '' || parent == x.type) {
                return or_res;
            }
            return "(" + or_res + ")";
        case 'Var':
            var v = x.name;
            var g = x.generation;
            return "".concat(v).concat(g);
    }
}
function addToSortedArray(arr, v) {
    var insertIndex = arr.length;
    for (var i = 0; i < arr.length; i++) {
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
function getBVars(x, acc) {
    switch (x.type) {
        case 'False':
            return acc;
        case 'True':
            return acc;
        case 'Not':
            return getBVars(x.op, acc);
        case 'And':
            return getBVars(x.op1, getBVars(x.op2, acc));
        case 'Or':
            return getBVars(x.op1, getBVars(x.op2, acc));
        case 'Var':
            return addToSortedArray(acc, { name: x.name, generation: x.generation });
    }
}
function isTrue(x) { return (x.type === 'True'); }
function isFalse(x) { return (x.type === 'False'); }
function isVarA(x) { return (x.type === 'Var') && x.name === 'a'; }
function isVarB(x) { return (x.type === 'Var') && x.name === 'b'; }
function buildVar(n, g) {
    return { type: 'Var', name: n, generation: g };
}
function buildAnd(x, y) {
    return { type: 'And', op1: x, op2: y };
}
function buildOr(x, y) {
    return { type: 'Or', op1: x, op2: y };
}
function buildNot(x) {
    if (isFalse(x)) {
        return True;
    }
    if (isTrue(x)) {
        return False;
    }
    if (x.type === 'Not') {
        return x.op;
    }
    else {
        return { type: 'Not', op: x };
    }
}
function equalBExp(x, y) {
    switch (x.type) {
        case 'False':
            return isFalse(y);
        case 'True':
            return isTrue(y);
        case 'Not':
            if (y.type == 'Not') {
                return equalBExp(x.op, y.op);
            }
            else {
                return false;
            }
        case 'And':
            if (y.type == 'And') {
                return equalBExp(x.op1, y.op1) && equalBExp(x.op2, y.op2);
            }
            else {
                return false;
            }
        case 'Or':
            if (y.type == 'Or') {
                return equalBExp(x.op1, y.op1) && equalBExp(x.op2, y.op2);
            }
            else {
                return false;
            }
        case 'Var':
            if (y.type == 'Var') {
                return x.name == y.name && x.generation == y.generation;
            }
            else {
                return false;
            }
    }
}
function buildIfThenElse(x, y, z) {
    if (equalBExp(y, z)) {
        return y;
    }
    if (isTrue(y) && isFalse(z)) {
        return x;
    }
    if (isFalse(y) && isTrue(z)) {
        return buildNot(x);
    }
    if (isFalse(z)) {
        return buildAnd(x, y);
    }
    if (isTrue(y)) {
        return buildOr(x, z);
    }
    if (isTrue(z)) {
        return buildOr(y, buildNot(x));
    }
    if (isFalse(y)) {
        return buildAnd(z, buildNot(x));
    }
    return buildOr(buildAnd(x, y), buildAnd(buildNot(x), z));
}
function getBVars8(ys) {
    return getBVars(ys.y1, getBVars(ys.y2, getBVars(ys.y3, getBVars(ys.y4, getBVars(ys.y5, getBVars(ys.y6, getBVars(ys.y7, getBVars(ys.y8, []))))))));
}
function evalBExp8(ys, env) {
    var count = 0;
    if (evalBExp(ys.y1, env)) {
        count++;
    }
    ;
    if (evalBExp(ys.y2, env)) {
        count++;
    }
    ;
    if (evalBExp(ys.y3, env)) {
        count++;
    }
    ;
    if (evalBExp(ys.y4, env)) {
        count++;
    }
    ;
    if (evalBExp(ys.y5, env)) {
        count++;
    }
    ;
    if (evalBExp(ys.y6, env)) {
        count++;
    }
    ;
    if (evalBExp(ys.y7, env)) {
        count++;
    }
    ;
    if (evalBExp(ys.y8, env)) {
        count++;
    }
    ;
    return count;
}
function golEval(vars, env, x, ys) {
    if (vars.length === 0) {
        var neighbors = evalBExp8(ys, env);
        var mid = evalBExp(x, env);
        var res = false;
        if (mid) {
            if (neighbors === 2 || neighbors === 3) {
                res = true;
            }
        }
        else {
            if (neighbors === 3) {
                res = true;
            }
        }
        return res ? True : False;
    }
    else {
        var newVars = vars.slice(1);
        var v = vars[0];
        var w = { type: 'Var', name: v.name, generation: v.generation };
        var envT = env.concat({ name: v.name, generation: v.generation, value: true });
        var envF = env.concat({ name: v.name, generation: v.generation, value: false });
        return buildIfThenElse(w, golEval(newVars, envT, x, ys), golEval(newVars, envF, x, ys));
    }
}
function countFalses(x, ys) {
    var count = 0;
    if (isFalse(x)) {
        count++;
    }
    ;
    if (isFalse(ys.y1)) {
        count++;
    }
    ;
    if (isFalse(ys.y2)) {
        count++;
    }
    ;
    if (isFalse(ys.y3)) {
        count++;
    }
    ;
    if (isFalse(ys.y4)) {
        count++;
    }
    ;
    if (isFalse(ys.y5)) {
        count++;
    }
    ;
    if (isFalse(ys.y6)) {
        count++;
    }
    ;
    if (isFalse(ys.y7)) {
        count++;
    }
    ;
    if (isFalse(ys.y8)) {
        count++;
    }
    ;
    return count;
}
function golCell(x, ys) {
    if (countFalses(x, ys) >= 7) {
        return False;
    }
    var vars = getBVars(x, getBVars8(ys));
    return golEval(vars, [], x, ys);
}
//console.log(golCell(True,{y1 : buildVar("b",2), y2 : buildVar("a",4), y3 : False, y4 : False,
//                           y5 : False, y6 : False, y7 : False, y8 : False}));
// ************************************************************************* //
//  Rest
// ************************************************************************* //
var miniSize = 30; // pixels
var marginSize = 2; // pixels
// Create the dropdown menu
var dropdown = document.createElement('select');
circuits.forEach(function (optionText) {
    var option = document.createElement('option');
    option.value = optionText.name;
    option.textContent = optionText.name;
    dropdown.appendChild(option);
});
document.body.appendChild(dropdown);
var step_button = document.createElement('button');
step_button.textContent = 'step';
step_button.id = 'step_button';
document.body.appendChild(step_button);
var step60_button = document.createElement('button');
step60_button.textContent = 'step 60';
step60_button.id = 'step60_button';
document.body.appendChild(step60_button);
var run_button = document.createElement('button');
run_button.textContent = 'run';
run_button.id = 'run_button';
document.body.appendChild(run_button);
var stop_button = document.createElement('button');
stop_button.textContent = 'stop';
stop_button.id = 'stop_button';
document.body.appendChild(stop_button);
var rotate_button = document.createElement('button');
rotate_button.textContent = 'rotate';
rotate_button.id = 'rotate_button';
document.body.appendChild(rotate_button);
document.body.appendChild(document.createElement('br'));
// Set up the canvas
var canvas = document.createElement('canvas');
canvas.width = 320 * 5; // Grid size in pixels
canvas.height = 320 * 5;
document.body.appendChild(canvas);
var ctx = canvas.getContext('2d');
if (!ctx) {
    throw new Error('Failed to get the canvas rendering context');
}
var paragraph = document.createElement("p");
paragraph.textContent = "This is a paragraph created from TypeScript.";
paragraph.style.fontFamily = "monospace";
document.body.appendChild(paragraph);
// Set up the canvas
var mini_canvas = document.createElement('canvas');
mini_canvas.width = 320 * 5; // Grid size in pixels
mini_canvas.height = 320 * 5;
document.body.appendChild(mini_canvas);
var mini_ctx = mini_canvas.getContext('2d');
if (!mini_ctx) {
    throw new Error('Failed to get the canvas rendering context');
}
// Parameters for the grid
var blockHeight = 1;
var blockWidth = 1;
var rows = 320; // Number of rows
var cols = 320; // Number of columns
var cellSize = canvas.width / cols; // Size of each cell
var updateInterval = 25; // Update interval in milliseconds
var black = '#000000';
// Create two grids (current and next state)
var grid = [];
var nextGrid = [];
var background = [];
var inputs = [];
var outputs = [];
var stepCount = 0;
var genCount = 0;
var allowRun = false;
var lastLoadedCircut = circuits[0];
var latestClick = { x: -500, y: -500 };
// Function to initialize the grid from an RLE string
function initializeFromRLE(rle, startRow, startCol, fill) {
    if (startRow === void 0) { startRow = 0; }
    if (startCol === void 0) { startCol = 0; }
    if (fill === void 0) { fill = True; }
    var lines = rle.split('\n');
    var row = startRow;
    var col = startCol;
    for (var _i = 0, lines_1 = lines; _i < lines_1.length; _i++) {
        var line = lines_1[_i];
        // Skip comment lines by checking the first character directly
        if (line[0] === '#')
            continue;
        var count = 0;
        for (var i = 0; i < line.length; i++) {
            var char = line.charAt(i);
            if (char >= '0' && char <= '9') {
                // Build the count from consecutive digits
                count = count * 10 + parseInt(char, 10);
            }
            else if (char === 'o') {
                // Alive cells
                if (count === 0)
                    count = 1; // Ensure count is at least 1
                var aliveCount = count;
                for (var i_1 = 0; i_1 < aliveCount; i_1++) {
                    if (row < rows && col < cols) {
                        grid[row][col] = fill;
                    }
                    col++;
                }
                count = 0;
            }
            else if (char === 'b') {
                // Dead cells
                if (count === 0)
                    count = 1; // Ensure count is at least 1
                var deadCount = count;
                col += deadCount;
                count = 0;
            }
            else if (char === '$') {
                // End of row
                if (count === 0)
                    count = 1; // Ensure count is at least 1
                row += count;
                col = startCol;
                count = 0;
            }
        }
    }
}
function drawTextBox(x, y, text) {
    if (!ctx) {
        return;
    }
    var padding = 10;
    var arrowHeight = 20;
    ctx.font = '16px Arial';
    var textMetrics = ctx.measureText(text);
    var textWidth = textMetrics.width;
    var textHeight = 16; // Approximate line height
    var bubbleWidth = textWidth + 2 * padding;
    var bubbleHeight = textHeight + 2 * padding;
    var bubbleX = x - bubbleWidth / 2;
    var bubbleY = y - bubbleHeight - arrowHeight;
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
    if (!ctx) {
        return;
    }
    ctx.clearRect(0, 0, canvas.width, canvas.height); // Clear the canvas
    for (var row = 0; row < rows; row++) {
        for (var col = 0; col < cols; col++) {
            var cell = grid[row][col];
            if (isTrue(cell)) {
                ctx.fillStyle = '#FFFFFF';
            }
            else if (isFalse(cell)) {
                ctx.fillStyle = background[row][col];
            }
            else if (isVarA(cell)) {
                ctx.fillStyle = '#FF0000';
            }
            else if (isVarB(cell)) {
                ctx.fillStyle = '#00FF00';
            }
            else {
                ctx.fillStyle = '#BF40BF';
            }
            ctx.fillRect(col * cellSize, row * cellSize, cellSize, cellSize);
        }
    }
    if (latestClick.x > -200) {
        var x = Math.floor(latestClick.x / cellSize);
        var y = Math.floor(latestClick.y / cellSize);
        //const text = `x: ${x}, y: ${y}`;
        var text = stringOfBExp(grid[y][x]);
        drawTextBox(latestClick.x, latestClick.y, text);
    }
}
function toX(x) { return x + 15 + 10; }
function toY(y) { return y + 15 + 10; }
function deleteBox(x, y, w, h) {
    for (var i = 0; i < w; i++) {
        for (var j = 0; j < h; j++) {
            grid[toY(y + j)][toX(x + i)] = False;
        }
    }
}
function getCell(row, col) {
    if (0 <= row && row < rows && 0 <= col && col < cols) {
        return grid[row][col];
    }
    else {
        return False;
    }
}
var varNames = ["a", "b", "c", "d"];
// Compute the next state of the grid
function computeNextState(ignoreInput) {
    var _a;
    if (ignoreInput === void 0) { ignoreInput = false; }
    for (var row = 0; row < rows; row++) {
        for (var col = 0; col < cols; col++) {
            var ns = {
                y1: getCell(row - 1, col + 1),
                y2: getCell(row - 1, col),
                y3: getCell(row - 1, col - 1),
                y4: getCell(row, col + 1),
                y5: getCell(row, col - 1),
                y6: getCell(row + 1, col + 1),
                y7: getCell(row + 1, col),
                y8: getCell(row + 1, col - 1),
            };
            nextGrid[row][col] = golCell(getCell(row, col), ns);
        }
    }
    // Swap grids (nextGrid becomes the current grid)
    _a = [nextGrid, grid], grid = _a[0], nextGrid = _a[1];
    if (stepCount == 59) {
        outputs.forEach(function (output) {
            if (output[1] == "E" || output[1] == "W") {
                var x = output[0][0];
                var y = output[0][1];
                deleteBox(15 * x - 6, 15 * y - 6, 12, 12);
            }
        });
        if (!ignoreInput) {
            inputs.forEach(function (input, index) {
                if (input[1] == "E") {
                    var x = input[0][0];
                    var y = input[0][1];
                    var v = buildVar(varNames[index], genCount);
                    initializeFromRLE("$5bo2bo$9bo$5bo3bo$6b4o!", toY(15 * y - 5), toX(15 * x - 5), v);
                }
                if (input[1] == "W") {
                    var x = input[0][0];
                    var y = input[0][1];
                    var v = buildVar(varNames[index], genCount);
                    initializeFromRLE("5$4o$o3bo$o$bo2bo!", toY(15 * y - 5), toX(15 * x - 5), v);
                }
            });
        }
    }
    if (stepCount == 29) {
        outputs.forEach(function (output) {
            if (output[1] == "N" || output[1] == "S" || output[1] == "EX" || output[1] == "EY") {
                var x = output[0][0];
                var y = output[0][1];
                deleteBox(15 * x - 6, 15 * y - 6, 12, 12);
            }
        });
        if (!ignoreInput) {
            inputs.forEach(function (input, index) {
                if (input[1] == "N") {
                    var x = input[0][0];
                    var y = input[0][1];
                    var v = buildVar(varNames[index], genCount);
                    initializeFromRLE("2b3o$bo2bo$4bo$4bo$bobo!", toY(15 * y - 5), toX(15 * x - 5), v);
                }
                if (input[1] == "S") {
                    var x = input[0][0];
                    var y = input[0][1];
                    var v = buildVar(varNames[index], genCount);
                    initializeFromRLE("5$6bobo$5bo$5bo$5bo2bo$5b3o!", toY(15 * y - 5), toX(15 * x - 5), v);
                }
                if (input[1] == "EX") {
                    var x = input[0][0];
                    var y = input[0][1];
                    var v = buildVar(varNames[index], genCount);
                    initializeFromRLE("3bo2bo$7bo$3bo3bo$4b4o", toY(15 * y - 5), toX(15 * x - 5), v);
                }
                if (input[1] == "EY") {
                    var x = input[0][0];
                    var y = input[0][1];
                    var v = buildVar(varNames[index], genCount);
                    initializeFromRLE("2bo2bo$6bo$2bo3bo$3b4o", toY(15 * y - 5), toX(15 * x - 5), v);
                }
            });
        }
    }
    stepCount = (stepCount + 1) % 60;
    if (stepCount === 0) {
        genCount++;
    }
}
// Animation loop with controlled update interval
var lastUpdateTime = 0; // Timestamp of the last update
function gameLoop(timestamp) {
    if (timestamp - lastUpdateTime >= updateInterval) {
        computeNextState();
        drawGrid();
        lastUpdateTime = timestamp; // Update the timestamp
    }
    if (allowRun) {
        requestAnimationFrame(gameLoop); // Loop the animation
    }
}
function colourBox(x, y, w, h, colour) {
    for (var i = 0; i < w; i++) {
        for (var j = 0; j < h; j++) {
            var real_x = toX(x + i);
            var real_y = toY(y + j);
            if (0 <= real_y && real_y < rows && 0 <= real_x && real_x < cols) {
                background[real_y][real_x] = colour;
            }
        }
    }
}
function updateBackground() {
    colourBox(-15, -15, 30 * blockWidth, 30 * blockHeight, '#000000');
    var port = '#444444';
    outputs.forEach(function (output) {
        var x = output[0][0];
        var y = output[0][1];
        colourBox(15 * x - 6, 15 * y - 6, 12, 12, port);
    });
    inputs.forEach(function (input) {
        var x = input[0][0];
        var y = input[0][1];
        colourBox(15 * x - 6, 15 * y - 6, 12, 12, port);
    });
}
function resizeGrid(width, height) {
    blockWidth = width;
    blockHeight = height;
    rows = height * 30 + 20;
    cols = width * 30 + 20;
    canvas.width = cols * 5;
    canvas.height = rows * 5;
    cellSize = canvas.width / cols;
    grid = [];
    nextGrid = [];
    background = [];
    stepCount = 0;
    genCount = 0;
    for (var row = 0; row < rows; row++) {
        grid[row] = [];
        nextGrid[row] = [];
        background[row] = [];
        for (var col = 0; col < cols; col++) {
            grid[row][col] = False;
            nextGrid[row][col] = False;
            background[row][col] = '#444444';
        }
    }
}
function drawMiniGate(x, y, rotate, ctxt, circuit) {
    var width = circuit.width;
    var height = circuit.height;
    var input_list = circuit.input;
    var output_list = circuit.output;
    var startX;
    var startY;
    var deltaX;
    var deltaY;
    var i;
    var _loop_1 = function () {
        var h = height;
        var w = width;
        width = h;
        height = w;
        input_list = input_list.map(function (elem) {
            return [[2 * (h - 1) - elem[0][1], elem[0][0]], rotateDir(elem[1])];
        });
        output_list = output_list.map(function (elem) {
            return [[2 * (h - 1) - elem[0][1], elem[0][0]], rotateDir(elem[1])];
        });
    };
    for (i = 0; i < rotate; i++) {
        _loop_1();
    }
    if (rotate % 4 == 0) {
        startX = x;
        startY = y;
        deltaX = 1;
        deltaY = 0;
    }
    else if (rotate % 4 == 1) {
        startX = x + width;
        startY = y;
        deltaX = 0;
        deltaY = 1;
    }
    else if (rotate % 4 == 2) {
        startX = x + width;
        startY = y + height;
        deltaX = -1;
        deltaY = 0;
    }
    else {
        startX = x;
        startY = y + height;
        deltaX = 0;
        deltaY = -1;
    }
    /* ctxt.fillRect(x * miniSize + marginSize,
                  y * miniSize + marginSize,
                  width * miniSize - marginSize,
                  height * miniSize - marginSize); */
    var chars = circuit.drawing.split('');
    ctxt.beginPath();
    ctxt.moveTo(startX * miniSize + 1, startY * miniSize + 1);
    i = 0;
    while (i < chars.length) {
        if (chars[i] == '-') {
            startX += deltaX;
            startY += deltaY;
            ctxt.lineTo(startX * miniSize + 1, startY * miniSize + 1);
        }
        else if (chars[i] == 'i') {
            ctxt.lineTo((startX + deltaX / 2 - deltaY / 3) * miniSize + 1, (startY + deltaY / 2 + deltaX / 3) * miniSize + 1);
            startX += deltaX;
            startY += deltaY;
            ctxt.lineTo(startX * miniSize + 1, startY * miniSize + 1);
        }
        else if (chars[i] == 'o') {
            ctxt.lineTo((startX + deltaX / 2 + deltaY / 3) * miniSize + 1, (startY + deltaY / 2 - deltaX / 3) * miniSize + 1);
            startX += deltaX;
            startY += deltaY;
            ctxt.lineTo(startX * miniSize + 1, startY * miniSize + 1);
        }
        else if (chars[i] == 'r') {
            var x_1 = deltaX;
            var y_1 = deltaY;
            deltaX = -y_1;
            deltaY = x_1;
        }
        else if (chars[i] == 'l') {
            var x_2 = deltaX;
            var y_2 = deltaY;
            deltaX = y_2;
            deltaY = -x_2;
        }
        i++;
    }
    ctxt.closePath();
    ctxt.globalAlpha = 0.5;
    ctxt.fill();
    ctxt.globalAlpha = 1.0;
    ctxt.stroke();
}
function drawMiniCircuit() {
    if (!mini_ctx) {
        throw new Error('Failed to get the canvas rendering context');
    }
    var width = lastLoadedCircut.width;
    var height = lastLoadedCircut.height;
    var mini_width = 2 * width + 2 * height + 5;
    var mini_height = 2 + Math.max(height, width);
    mini_canvas.width = miniSize * mini_width + marginSize;
    mini_canvas.height = miniSize * mini_height + marginSize;
    mini_ctx.fillStyle = 'black';
    mini_ctx.fillRect(0, 0, mini_canvas.width, mini_canvas.height); // Clear the canvas
    mini_ctx.fillStyle = '#444444';
    for (var row = 0; row < mini_height; row++) {
        for (var col = 0; col < mini_width; col++) {
            mini_ctx.fillRect(col * miniSize + marginSize, row * miniSize + marginSize, miniSize - marginSize, miniSize - marginSize);
        }
    }
    mini_ctx.fillStyle = 'yellow';
    mini_ctx.strokeStyle = 'yellow';
    drawMiniGate(1, 1, 0, mini_ctx, lastLoadedCircut);
    drawMiniGate(2 + width, 1, 1, mini_ctx, lastLoadedCircut);
    drawMiniGate(3 + width + height, 1, 2, mini_ctx, lastLoadedCircut);
    drawMiniGate(4 + 2 * width + height, 1, 3, mini_ctx, lastLoadedCircut);
}
function loadCircuit(circuit) {
    lastLoadedCircut = circuit;
    var rleContent = circuit.content;
    inputs = circuit.input;
    outputs = circuit.output;
    paragraph.textContent = circuit.name + ' 3 4 red 2';
    resizeGrid(circuit.width, circuit.height);
    updateBackground();
    initializeFromRLE(rleContent, 10, 10);
    drawGrid();
    drawMiniCircuit();
}
// Function to handle dropdown changes
function handleDropdownChange(event) {
    var selectedValue = event.target.value;
    circuits.forEach(function (circuit) {
        if (circuit.name == selectedValue) {
            loadCircuit(circuit);
        }
    });
}
loadCircuit(circuits[0]);
dropdown.addEventListener('change', handleDropdownChange);
step_button.addEventListener('click', function () {
    computeNextState();
    drawGrid();
});
step60_button.addEventListener('click', function () {
    for (var k = 0; k < 60; k++) {
        computeNextState();
    }
    drawGrid();
});
run_button.addEventListener('click', function () {
    allowRun = true;
    latestClick = { x: -500, y: -500 };
    requestAnimationFrame(gameLoop);
});
stop_button.addEventListener('click', function () {
    allowRun = false;
});
function rotateDir(dir) {
    if (dir == "E") {
        return "S";
    }
    if (dir == "S") {
        return "W";
    }
    if (dir == "W") {
        return "N";
    }
    return "E";
}
rotate_button.addEventListener('click', function () {
    if (stepCount > 0) {
        loadCircuit(lastLoadedCircut);
    }
    var tempGrid = [];
    for (var i = 0; i < cols; i++) {
        tempGrid[i] = [];
        for (var j = 0; j < rows; j++) {
            tempGrid[i][j] = grid[(rows - 1) - j][i];
        }
    }
    inputs = inputs.map(function (elem) {
        return [[2 * (blockHeight - 1) - elem[0][1], elem[0][0]], rotateDir(elem[1])];
    });
    outputs = outputs.map(function (elem) {
        return [[2 * (blockHeight - 1) - elem[0][1], elem[0][0]], rotateDir(elem[1])];
    });
    resizeGrid(blockHeight, blockWidth);
    updateBackground();
    grid = tempGrid;
    for (var k = 0; k < 30; k++) {
        computeNextState(true);
    }
    outputs.forEach(function (output) {
        var x = output[0][0];
        var y = output[0][1];
        deleteBox(15 * x - 6, 15 * y - 6, 12, 12);
    });
    stepCount = 0;
    genCount = 0;
    allowRun = false;
    drawGrid();
});
canvas.addEventListener('mousemove', function (event) {
    var rect = canvas.getBoundingClientRect();
    latestClick = {
        x: event.clientX - rect.left,
        y: event.clientY - rect.top,
    };
    drawGrid();
});
canvas.addEventListener('click', function (event) {
    var rect = canvas.getBoundingClientRect();
    latestClick = {
        x: event.clientX - rect.left,
        y: event.clientY - rect.top,
    };
    drawGrid();
});
canvas.addEventListener('mouseleave', function (event) {
    latestClick = { x: -500, y: -500 };
    drawGrid();
});
// ************************************************************************* //
//  Circuit canvas
// ************************************************************************* //
var circ_width = 30; // Number of rows
var circ_height = 30; // Number of columns
document.body.appendChild(document.createElement('br'));
var circ_textarea = document.createElement('textarea');
circ_textarea.rows = 40;
circ_textarea.cols = 40;
circ_textarea.style.fontFamily = "monospace";
circ_textarea.value = "\nwidth 30\nheight 30\nGenerate2_E 10 28 red 3\nGenerate1_E 12 28 red 3\nGenerate1_E 14 28 red 3\nGenerate1_E 16 28 red 3\nvwire 11 28 -16\nvwire 12 28 -18\nvwire 14 28 -16\nvwire 16 28 -16\nU_turn_WN_EXN 8 26 red 0\nU_turn_WN_EXN 8 24 red 0\nU_turn_WN_EXN 8 14 red 0\nU_turn_WN_EXN 8 12 red 0\nhwire 12 13 5 red\nhwire 12 15 5 red\nhwire 7 16 10 red\nhwire 4 17 13 red\nhwire 3 22 14 red\nhwire 8 23 9 red\nhwire 12 25 5 red\nhwire 12 27 5 red\nGenerate2_EX 5 15 red 0\nGenerate2_EX 2 16 red 0\nGenerate2_EX 1 21 red 0\nTurn_E_S 0 23 blue 1\nDuplicate_E_EN 24 22 blue 2\nhwire 24 24 -12\nhwire 30 26 -18\nhwire 30 24 -2\nvwire 25 26 4\nvwire 3 30 -8\nhwire 4 26 -4\nvwire 23 17 13\nvwire 0 4 19\nhwire 0 9 1\nvwire 4 13 5\nvwire 7 7 10\nhwire 0 6 6\nTurn_E_S 6 4 blue 0\nNot_turn_EX_N 22 15 blue 2\nhwire 28 16 -3 red\nhwire 25 14 -13 \nhwire 22 12 -10\nTurn_Middle_E_S 22 10 blue 1\nTurn_E_S 25 13 blue 1\nvwire 25 0 13\nvwire 23 0 4\nvwire 23 8 2\nhwire 25 6 5\nDuplicate_E_EN 21 4 blue 1\nDuplicate_E_EN 26 7 blue 1\nvwire 28 11 5\nvwire 28 4 3\nhwire 16 3 11\nGenerate1_E 14 3 yellow 0\nGenerate1_EX 15 0 yellow 1\nGenerate2_E 12 4 orange 0\nvwire 16 2 2 red\nvwire 17 6 -4 red\nhwire 14 5 6 red\nhwire 18 2 -5\nDuplicate_E_EN 9 0 blue 2\nvwire 10 4 2 \nvwire 14 6 -1 \nvwire 16 10 -5\nvwire 3 8 -8\nvwire 5 1 -1\nhwire 9 2 -1\nhwire 4 2 -1\nNot_turn_N_EX 28 16 blue 2\ncolor grey\nDuplicate_N_WEX 4 23 red 0\nAnd_Not_And_Not_NNS_N 10 6 orange 0\nAnd_Not_NN_NN 13 10 orange 0\nAnd_Wire_Wire_EWN_EWN 19 17 lime 0\nDuplicate_E_ES 18 21 lime 2\nBefore_Latch_EYN_NN 17 4 yellow 0\nU_turn2_W_E 1 18 lime 0\nU_turn2_W_E 26 18 lime 2\nU_turn_W_E 3 20 lime 0\nU_turn_W_E 26 20 lime 2\nhwire 5 18 21\nhwire 26 19 -21\nhwire 7 20 29\nhwire 26 21 -19\nvwire 19 21 -1 \nvwire 19 17 -6 \nvwire 19 4 -1\nAnd_Not_NW_W 17 0 yellow 0\nGenerate1_E 20 1 yellow 2\nNot_Turn_E_S 27 1 blue 0\nNot_Turn_E_N 0 0 blue 2\nFork_Not_WN_WN 4 1 blue 0\nbox 1 8 5 5\nvwire 5 30 -1\n";
document.body.appendChild(circ_textarea);
document.body.appendChild(document.createElement('br'));
var circ_button = document.createElement('button');
circ_button.textContent = 'update circuit';
circ_button.id = 'circ_button';
document.body.appendChild(circ_button);
document.body.appendChild(document.createElement('br'));
// Set up the circuit canvas
var circ_canvas = document.createElement('canvas');
circ_canvas.width = 5;
circ_canvas.height = 5;
document.body.appendChild(circ_canvas);
var circ_ctx = circ_canvas.getContext('2d');
if (!circ_ctx) {
    throw new Error('Failed to get the canvas rendering context');
}
function drawArrow(ctx, fromX, fromY, toX, toY) {
    var headLength = 11; // length of arrowhead
    var dx = toX - fromX;
    var dy = toY - fromY;
    var angle = Math.atan2(dy, dx);
    // Draw main line
    ctx.beginPath();
    ctx.moveTo(fromX, fromY);
    ctx.lineTo(toX, toY);
    ctx.stroke();
    // Draw arrowhead
    ctx.beginPath();
    ctx.moveTo(toX, toY);
    ctx.lineTo(toX - headLength * Math.cos(angle - Math.PI / 6), toY - headLength * Math.sin(angle - Math.PI / 6));
    ctx.lineTo(toX - headLength * Math.cos(angle + Math.PI / 6), toY - headLength * Math.sin(angle + Math.PI / 6));
    ctx.lineTo(toX, toY);
    ctx.fill();
}
// Draw the grid on the canvas
function drawCircuit() {
    if (!circ_ctx) {
        return;
    }
    var lines = circ_textarea.value
        .split(/\r?\n/)
        .map(function (line) { return line.trim().split(/\s+/); });
    lines.forEach(function (words) {
        if (words.length > 0) {
            if (words[0] == 'width' && words.length == 2) {
                circ_width = Number(words[1]);
            }
            if (words[0] == 'height' && words.length == 2) {
                circ_height = Number(words[1]);
            }
        }
    });
    circ_canvas.width = miniSize * circ_width + marginSize;
    circ_canvas.height = miniSize * circ_height + marginSize;
    circ_ctx.fillStyle = 'black';
    circ_ctx.fillRect(0, 0, circ_canvas.width, circ_canvas.height); // Clear the canvas
    circ_ctx.fillStyle = '#444444';
    circ_ctx.strokeStyle = '#777777ff';
    for (var row = 0; row < circ_height; row++) {
        for (var col = 0; col < circ_width; col++) {
            var cell = grid[row][col];
            circ_ctx.fillRect(col * miniSize + marginSize, row * miniSize + marginSize, miniSize - marginSize, miniSize - marginSize);
            circ_ctx.strokeText(col.toString(), col * miniSize + marginSize * 4, row * miniSize + marginSize + 12);
            circ_ctx.strokeText(row.toString(), col * miniSize + marginSize * 4, row * miniSize + marginSize + 22);
        }
    }
    var color = '#3a5bb7ff';
    // draw boxes
    lines.forEach(function (words) {
        if (words.length > 0) {
            if (words[0] == 'color' && words.length == 2) {
                color = words[1];
            }
            if (words[0] == 'box' && words.length == 5) {
                var x = Number(words[1]);
                var y = Number(words[2]);
                var w = Number(words[3]);
                var h = Number(words[4]);
                circ_ctx.fillStyle = color;
                circ_ctx.fillRect(x * miniSize + marginSize, y * miniSize + marginSize, w * miniSize - marginSize, h * miniSize - marginSize);
            }
        }
    });
    // draw arrows 
    lines.forEach(function (words) {
        if (words.length > 0) {
            if (words[0] == 'hwire' && words.length >= 4) {
                var x = Number(words[1]);
                var y = Number(words[2]);
                var l = Number(words[3]);
                circ_ctx.lineWidth = 3;
                circ_ctx.fillStyle = 'white';
                circ_ctx.strokeStyle = 'white';
                if (words.length >= 5) {
                    circ_ctx.fillStyle = 'red';
                    circ_ctx.strokeStyle = 'red';
                }
                if (l < 0) {
                    drawArrow(circ_ctx, x * miniSize, y * miniSize + miniSize / 2, (x + l) * miniSize + marginSize, y * miniSize + miniSize / 2);
                }
                else {
                    drawArrow(circ_ctx, x * miniSize + marginSize, y * miniSize + miniSize / 2, (x + l) * miniSize, y * miniSize + miniSize / 2);
                }
            }
            if (words[0] == 'vwire' && words.length >= 4) {
                var x = Number(words[1]);
                var y = Number(words[2]);
                var l = Number(words[3]);
                circ_ctx.lineWidth = 3;
                circ_ctx.fillStyle = 'white';
                circ_ctx.strokeStyle = 'white';
                if (words.length >= 5) {
                    circ_ctx.fillStyle = 'red';
                    circ_ctx.strokeStyle = 'red';
                }
                if (l < 0) {
                    drawArrow(circ_ctx, x * miniSize + miniSize / 2, y * miniSize, x * miniSize + miniSize / 2, (y + l) * miniSize + marginSize);
                }
                else {
                    drawArrow(circ_ctx, x * miniSize + miniSize / 2, y * miniSize + marginSize, x * miniSize + miniSize / 2, (y + l) * miniSize);
                }
            }
        }
    });
    // draw gates
    lines.forEach(function (words) {
        if (words.length > 4) {
            circuits.forEach(function (c) {
                if (c.name == words[0]) {
                    var x = Number(words[1]);
                    var y = Number(words[2]);
                    var r = Number(words[4]);
                    circ_ctx.fillStyle = words[3];
                    circ_ctx.strokeStyle = words[3];
                    drawMiniGate(x, y, r, circ_ctx, c);
                }
            });
        }
    });
}
drawCircuit();
circ_button.addEventListener('click', function () {
    drawCircuit();
});
