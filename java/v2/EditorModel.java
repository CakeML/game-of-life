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

    public EditorModel(String rle) {
        golState = new GOLState(rle);
        bg = new Grid2DBackground();
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
        genCount++;
    }

    public void tick() {
        golState = golState.tick();
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
