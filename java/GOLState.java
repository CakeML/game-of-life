import java.util.*;

public class GOLState {

    private static final BoolExp defaultFalse = new BoolFalse();
    private static final BoolExp defaultTrue = new BoolTrue();

    private Map<Point2D,BoolExp> cells;

    public GOLState() {
        cells = new TreeMap<Point2D,BoolExp>();
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
            ret.setCell(p,tickValOf(p));
        }
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
        String[] vs = (String[])vars.toArray();
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
