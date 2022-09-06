import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

public class Gate {

    public enum Direction {
        NORTH, SOUTH, EAST, WEST
    }

    private int x;
    private int y;
    private Direction dir = Direction.SOUTH;
    private boolean isInGate;
    private String varName = "a";
    private int k = 0;

    public Gate(int x, int y, boolean isInGate) {
        this.x = x;
        this.y = y;
        this.isInGate = isInGate;
    }

    public void nextVersion() {
        switch (k) {
            case 0: dir = Direction.EAST; break;
            case 1: dir = Direction.NORTH; break;
            case 2: dir = Direction.WEST; break;
            case 3: dir = Direction.SOUTH; varName = "b"; break;
            case 4: dir = Direction.EAST; break;
            case 5: dir = Direction.NORTH; break;
            case 6: dir = Direction.WEST; break;
            case 7: dir = Direction.SOUTH; varName = "a"; k = 0; break;
        }
        k++;
    }

    private boolean hitThisGate(int x, int y) {
        return Math.abs(x - this.x) < 3 && Math.abs(y - this.y) < 3;
    }

    // returns true if this hit this gate
    public boolean click(int x, int y) {
        if (hitThisGate(x,y)) {
            nextVersion();
            return true;
        } else {
            return false;
        }
    }

    private Direction opposite(Direction d) {
        switch (d) {
            case NORTH: return Direction.SOUTH;
            case SOUTH: return Direction.NORTH;
            case EAST: return Direction.WEST;
            case WEST: return Direction.EAST;
        }
        return null;
    }

    private Direction cond_opp(Direction d) {
        if (isInGate) { return d; }
        return opposite(d);
    }

    private final Color aDarkColor = new Color(255,55,55);
    private final Color bDarkColor = new Color(55,255,55);
    private final Color outGateColor = new Color(155,155,155);

    public Color colorAt(int x, int y) {
        if (hitThisGate(x,y)) {
            int i = this.x - x;
            int j = this.y - y;
            switch (cond_opp(dir)) {
                case EAST:
                    if (j == 0) { break; }
                    if (j == 1 && i == -1) { break; }
                    if (j == 2 && i == 0) { break; }
                    if (j == -1 && i == -1) { break; }
                    if (j == -2 && i == 0) { break; }
                    return null;
                case WEST:
                    if (j == 0) { break; }
                    if (j == 1 && i == 1) { break; }
                    if (j == 2 && i == 0) { break; }
                    if (j == -1 && i == 1) { break; }
                    if (j == -2 && i == 0) { break; }
                    return null;
                case NORTH:
                    if (i == 0) { break; }
                    if (i == 1 && j == 1) { break; }
                    if (i == 2 && j == 0) { break; }
                    if (i == -1 && j == 1) { break; }
                    if (i == -2 && j == 0) { break; }
                    return null;
                case SOUTH:
                    if (i == 0) { break; }
                    if (i == 1 && j == -1) { break; }
                    if (i == 2 && j == 0) { break; }
                    if (i == -1 && j == -1) { break; }
                    if (i == -2 && j == 0) { break; }
                    return null;
            }
            if (!isInGate) {
                return outGateColor;
            }
            if (varName.equals("a")) {
                return aDarkColor;
            } if (varName.equals("b")) {
                return bDarkColor;
            } else {
                return Color.BLUE;
            }
        } else {
            return null;
        }
    }

    private final BoolExp defaultFalse = new BoolFalse();

    public void modifyGOLState(GOLState golState, int genCount) {
        for (int j=-3;j<=3; j++) {
            for (int i=-3;i<=3; i++) {
                golState.setCell(x+i,y+j,defaultFalse);
            }
        }
        BoolVar var = new BoolVar(varName + genCount);
        Direction d = dir;
        if (!isInGate) { var = null; d = opposite(dir); }
        switch (d) {
            case EAST:
                golState.setCell(x,y,var);
                golState.setCell(x+1,y+1,var);
                golState.setCell(x+2,y+1,var);
                golState.setCell(x+3,y+1,var);
                golState.setCell(x+4,y+1,var);
                golState.setCell(x+4,y,var);
                golState.setCell(x+4,y-1,var);
                golState.setCell(x+3,y-2,var);
                golState.setCell(x,y-2,var);
                return;
            case WEST:
                golState.setCell(x-1,y+3,var);
                golState.setCell(x-1,y+5,var);
                golState.setCell(x-2,y+2,var);
                golState.setCell(x-3,y+2,var);
                golState.setCell(x-4,y+2,var);
                golState.setCell(x-5,y+2,var);
                golState.setCell(x-5,y+3,var);
                golState.setCell(x-5,y+4,var);
                golState.setCell(x-4,y+5,var);
                return;
            case NORTH:
                golState.setCell(x,y+16,var);
                golState.setCell(x-2,y+16,var);
                golState.setCell(x-3,y+15,var);
                golState.setCell(x-3,y+14,var);
                golState.setCell(x-3,y+13,var);
                golState.setCell(x-3,y+12,var);
                golState.setCell(x-2,y+12,var);
                golState.setCell(x-1,y+12,var);
                golState.setCell(x,y+13,var);
                return;
            case SOUTH:
                golState.setCell(x-1,y-13,var);
                golState.setCell(x+1,y-13,var);
                golState.setCell(x+2,y-12,var);
                golState.setCell(x+2,y-11,var);
                golState.setCell(x+2,y-10,var);
                golState.setCell(x+2,y-9,var);
                golState.setCell(x+1,y-9,var);
                golState.setCell(x,y-9,var);
                golState.setCell(x-1,y-10,var);
                return;
        }
        return;
    }

}
