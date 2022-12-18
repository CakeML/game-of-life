import java.util.*;

public class GOLState {

    private static final BoolExp defaultFalse = new BoolFalse();
    private static final BoolExp defaultTrue = new BoolTrue();

    private Map<Point2D,BoolExp> cells;

    public GOLState() {
        cells = new TreeMap<Point2D,BoolExp>();
    }

    public GOLState(String rle) {
        this();
        readRLE(rle);
    }

    private boolean isSet(Point2D p, TreeMap<Point2D,BoolExp> cs) {
        BoolExp b = cs.get(p);
        if (b == null) { return false; }
        return b instanceof BoolTrue;
    }

    private boolean isSet(int x, int y, Point2D p, TreeMap<Point2D,BoolExp> cs) {
        Point2D q = new Point2D(x + p.getX(), y + p.getY());
        return isSet(q,cs);
    }

    private boolean isClear(Point2D p, TreeMap<Point2D,BoolExp> cs) {
        BoolExp b = cs.get(p);
        if (b == null) { return true; }
        return b instanceof BoolFalse;
    }

    private boolean isClear(int x, int y, Point2D p, TreeMap<Point2D,BoolExp> cs) {
        Point2D q = new Point2D(x + p.getX(), y + p.getY());
        return isClear(q,cs);
    }

    private boolean hasSpecialPattern(Point2D p, TreeMap<Point2D,BoolExp> cs) {
        // ...
        // .x.
        // ...
        // .x.   <-- that x is the position of the marker
        // ..x
        return isSet(p,cs) &&
               isSet(1,1,p,cs) &&
               isSet(0,-2,p,cs) &&
               isClear(-1,-1,p,cs) &&
               isClear( 0,-1,p,cs) &&
               isClear( 1,-1,p,cs) &&
               isClear(-1, 0,p,cs) &&
               isClear( 1, 0,p,cs) &&
               isClear(-1, 1,p,cs) &&
               isClear( 0, 1,p,cs);
    }

    private void readRLE(String rle) {
        TreeMap<Point2D,BoolExp> newCells = new TreeMap<Point2D,BoolExp>();
        if (rle == null) { return; }
        int i = 0;
        int len = rle.length();
        int x = 0;
        int y = 0;
        int rep = 1;
        while (i < len) {
            Character c = rle.charAt(i);
            if (c == 'b') {
                x = x + rep;
            } else if (c == 'o') {
                for (int k=0; k < rep; k++) {
                    newCells.put(new Point2D(x,y),defaultTrue);
                    x++;
                }
            } else if (c == '$') {
                x = 0;
                y = y + rep;
            } else if (c == '!') {
                break;
            } else if ('0' <= c && c <= '9') {
                int j = i+1;
                while (j < len && '0' <= rle.charAt(j) && rle.charAt(j) <= '9') { j++; }
                rep = Integer.parseInt(rle.substring(i,j));
                i = j;
                continue;
            }
            i++;
            rep = 1;
        }
        int midX = x/2;
        int midY = y/2;
        // attempt to find special marker pattern for (0,0)
        Set<Point2D> allPoints = newCells.keySet();
        for (Point2D p : allPoints) {
            if (hasSpecialPattern(p,newCells)) {
                midX = p.getX();
                midY = p.getY();
                break;
            }
        }
        cells = translate(-midX,-midY,newCells);
    }

    public void setCell(int x, int y, BoolExp b) {
        setCell(new Point2D(x,y), b);
    }

    public void setCell(Point2D p, BoolExp b) {
        if (b == null || b instanceof BoolFalse) {
            cells.remove(p);
        }
        cells.put(p,b);
    }

    public BoolExp cell(int x, int y) {
        return cell(new Point2D(x,y));
    }

    public BoolExp cell(Point2D p) {
        BoolExp b = cells.get(p);
        if (b == null) { return defaultFalse; }
        return b;
    }

    public Set<Point2D> points() {
        return cells.keySet();
    }

    public String toString() {
        String ret = "GOLState = (\n";
        for (Map.Entry<Point2D,BoolExp> entry : cells.entrySet()) {
            ret += "  " + entry.getKey().toString() + " = " + entry.getValue() + "\n";
        }
        return ret + ")\n";
    }

    public String toHOLString() {
        String ret = "     [";
        boolean isFirst = true;
        for (Map.Entry<Point2D,BoolExp> entry : cells.entrySet()) {
            BoolExp v = entry.getValue();
            if (v == null) { continue; }
            String v_str = v.toString();
            if (v_str.equals("F")) { continue; }
            if (!isFirst) { ret += ",\n      "; }
            ret += "(" + entry.getKey().toString() + ", " + v_str + ")";
            isFirst = false;
        }
        return ret + "]\n";
    }

    private TreeMap<Point2D,BoolExp> translate(int dx, int dy, Map<Point2D,BoolExp> old) {
        TreeMap<Point2D,BoolExp> ret = new TreeMap<Point2D,BoolExp>();
        for (Map.Entry<Point2D,BoolExp> entry : old.entrySet()) {
            Point2D p = entry.getKey();
            ret.put(new Point2D(p.getX() + dx, p.getY() + dy), entry.getValue());
        }
        return ret;
    }

    public GOLState translate(int dx, int dy) {
        GOLState ret = new GOLState();
        ret.cells = translate(dx, dy, cells);
        return ret;
    }

    // returns a new state following the rules of Game of Life
    public GOLState tick() {
        GOLState ret = new GOLState();
        // make a set of points of interest
        Set<Point2D> toVisit = new TreeSet<Point2D>();
        for (Map.Entry<Point2D,BoolExp> entry : cells.entrySet()) {
            Point2D p = entry.getKey();
            toVisit.add(p);
            addNeighbouringPoints(p,toVisit);
        }
        // insert new state for each point in toVisit
        for (Point2D p : toVisit) {
            BoolExp e = tickValOf(p);
            if (!(e instanceof BoolFalse)) {
                ret.setCell(p,e);
            }
        }
        // print debug output
        //System.out.println("------------------------------------");
        //System.out.println(this.toString());
        // return the resulting GOLState
        return ret;
    }

    // used by tick
    private void addNeighbouringPoints(Point2D p, Set<Point2D> s) {
        int x = p.getX();
        int y = p.getY();
        s.add(new Point2D(x-1,y-1));
        s.add(new Point2D(x  ,y-1));
        s.add(new Point2D(x+1,y-1));
        s.add(new Point2D(x-1,y  ));
        //    new Point2D(x  ,y  )
        s.add(new Point2D(x+1,y  ));
        s.add(new Point2D(x-1,y+1));
        s.add(new Point2D(x  ,y+1));
        s.add(new Point2D(x+1,y+1));
    }

    // used by tick
    private BoolExp tickValOf(Point2D p) {
        // make set of all neighbouring points
        Set<Point2D> surrounding = new TreeSet<Point2D>();
        addNeighbouringPoints(p,surrounding);
        // collect vars from all neighbouring cells
        Set<String> vars = new TreeSet<String>();
        cell(p).addVars(vars);
        for (Point2D xy : surrounding) {
            cell(xy).addVars(vars);
        }
        String[] vs = new String[vars.toArray().length];
        int i = 0;
        for (String s : vars) {
            vs[i++] = s;
        }
        // now build expression
        Map<String,Boolean> varMapping = new TreeMap<String,Boolean>();
        return buildBoolExp(0,vs,p,surrounding,varMapping);
    }

    // used by tickValOf
    private BoolExp buildBoolExp(int i, String[] vs, Point2D p,
                                 Set<Point2D> surrounding,
                                 Map<String,Boolean> varMapping) {
        if (i < vs.length) {
            String v = vs[i];
            BoolExp e0 = new BoolVar(v);
            varMapping.put(v,true);
            BoolExp e1 = buildBoolExp(i+1,vs,p,surrounding,varMapping);
            varMapping.put(v,false);
            BoolExp e2 = buildBoolExp(i+1,vs,p,surrounding,varMapping);
            return BoolIf.make(e0,e1,e2);
        }
        int liveCount = 0;
        for (Point2D xy : surrounding) {
            boolean live = cell(xy).eval(varMapping);
            if (live) { liveCount++; }
        }
        boolean pIsLive = cell(p).eval(varMapping);
        if (pIsLive) {
            if (liveCount == 2 || liveCount == 3) {
                return defaultTrue;
            } else {
                return defaultFalse;
            }
        } else {
            if (liveCount == 3) {
                return defaultTrue;
            } else {
                return defaultFalse;
            }
        }
    }

}
