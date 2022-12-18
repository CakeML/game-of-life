import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import java.util.*;

public class EditorModel implements GridModel {

    private GOLState golState;
    private Grid2DBackground bg;
    private LinkedList<Gate> gates = new LinkedList<Gate>();
    private int genCount = 0;
    private int varCount = 0;
    private LinkedList<GOLState> history = new LinkedList<GOLState>();

    private boolean onlyNWSE(String str) {
        for (int i=0; i<str.length(); i++) {
            if (str.charAt(i) == 'n') continue;
            if (str.charAt(i) == 'w') continue;
            if (str.charAt(i) == 's') continue;
            if (str.charAt(i) == 'e') continue;
            System.out.println("Bad in/out char: " + str.substring(i,i+1));
            return false;
        }
        return true;
    }

    private void addGate(int x, int y, boolean isInGate, Gate.Direction dir, String varName) {
        x = Grid2DBackground.getGateX(x);
        y = Grid2DBackground.getGateX(y);
        Gate g = new Gate(x,y,isInGate,dir,varName);
        gates.add(g);
    }

    private void autoGates(String name) {
        int i1 = 0;
        int i2 = 0;
        int i3 = 0;
        for (int i=0; i<name.length(); i++) {
            if (name.charAt(i) == '-') {
                i1 = i2;
                i2 = i3;
                i3 = i;
            }
            if (name.charAt(i) == '.') {
                i1 = i2;
                i2 = i3;
                i3 = i;
                break;
            }
        }
        String input = name.substring(i1+1,i2);
        String output = name.substring(i2+1,i3);
        if (!onlyNWSE(input)) { return; }
        if (!onlyNWSE(output)) { return; }
        String varName = "a";
        if (input.contains("e")) { addGate(0,0,true,Gate.Direction.EAST,varName); varName = "b"; }
        if (input.contains("s")) { addGate(75,-75,true,Gate.Direction.SOUTH,varName); varName = "b"; }
        if (input.contains("n")) { addGate(75,75,true,Gate.Direction.NORTH,varName); varName = "b"; }
        if (input.contains("w")) { addGate(150,0,true,Gate.Direction.WEST,varName); varName = "b"; }
        if (output.contains("e")) { addGate(150,0,false,Gate.Direction.WEST,varName); }
        if (output.contains("s")) { addGate(75,75,false,Gate.Direction.NORTH,varName); }
        if (output.contains("n")) { addGate(75,-75,false,Gate.Direction.SOUTH,varName); }
        if (output.contains("w")) { addGate(0,0,false,Gate.Direction.EAST,varName); }
    }

    public EditorModel(String name, String rle) {
        golState = new GOLState(rle);
        bg = new Grid2DBackground();
        autoGates(name);
    }

    private Color getGateColor(int x, int y) {
        if (!Grid2DBackground.isGatePos(x,y)) { return null; }
        for (Gate gate : gates) {
            Color gc = gate.colorAt(x,y);
            if (gc != null) { return gc; }
        }
        return null;
    }

    public String cellInfo(int x, int y) {
        return golState.cell(x,y).toString();
    }

    private final Color aGlider = new Color(255,100,100);
    private final Color bGlider = new Color(150,255,150);
    private final Color tGlider = new Color(100,100,255);

    public Color cell(int x, int y) {
        BoolExp b = golState.cell(x,y);
        if (b instanceof BoolFalse) {
            Color gc = getGateColor(x,y);
            if (gc == null) {
                return bg.cell(x,y);
            } else {
                return gc;
            }
        } else if (b instanceof BoolTrue) {
            return Color.WHITE;
        } else if (b instanceof BoolVar) {
            BoolVar var = (BoolVar)b;
            String n = var.getName();
            if (n.startsWith("a")) {
                return aGlider;
            } else if (n.startsWith("b")) {
                return bGlider;
            } else if (n.startsWith("t")) {
                return tGlider;
            }
            return Color.YELLOW;
        } else {
            return Color.MAGENTA;
        }
    }

    public void startSim() {
        for (Gate gate : gates) {
            gate.modifyGOLState(golState,genCount);
        }
        history = new LinkedList<GOLState>();
        history.add(golState);
        genCount++;
    }

    public void tick() {
        golState = golState.tick();
        history.add(golState);
    }

    public void translate(int x, int y) {
        golState = golState.translate(x,y);
    }

    public boolean gateClick(int x, int y, boolean isInGate) {
        if (!Grid2DBackground.isGatePos(x,y)) { return false; }
        for (Gate gate : gates) {
            if (gate.click(x,y)) {
                return true;
            }
        }
        x = Grid2DBackground.getGateX(x);
        y = Grid2DBackground.getGateX(y);
        Gate g = new Gate(x,y,isInGate);
        gates.add(g);
        return true;
    }

    public void rename() {
        Set<Point2D> all = golState.points();
        HashMap<String,BoolVar> map = new HashMap<String,BoolVar>();
        for (Point2D p : all) {
            BoolExp e = golState.cell(p);
            if (e instanceof BoolTrue) { continue; }
            if (e instanceof BoolFalse) { continue; }
            String k = e.toString();
            BoolVar v = map.get(k);
            if (v == null) {
                v = new BoolVar("t" + varCount);
                map.put(k,v);
                varCount++;
            }
            golState.setCell(p,v);
        }
    }

}
