import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import java.util.*;

public class EditorModel implements GridModel {

    private GOLState golState;
    private Grid2DBackground bg;
    private LinkedList<Gate> gates = new LinkedList<Gate>();

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

    public Color cell(int x, int y) {
        BoolExp b = golState.cell(x,y);
        if (b instanceof BoolFalse) {
            Color gc = getGateColor(x,y);
            if (gc == null) {
                return bg.cell(x,y);
            } else {
                return gc;
            }
        } else {
            return Color.WHITE;
        }
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

}
