import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

public class Grid2DBackground implements GridModel {

    public static boolean isGatePos(int i, int j) {
        if (i < 0) { i = -i; }
        if (j < 0) { j = -j; }
        i = i + 2;
        j = j + 2;
        if ((i % 15 < 5) && (j % 15 < 5)) {
            return ((i / 15 + j / 15) % 2 == 0);
        } else {
            return false;
        }
    }

    public static int getGateX(int x) {
        if (x < 0) { x = x-2; } else { x = x+2; }
        return (x / 15) * 15;
    }

    public static int getGateY(int y) {
        if (y < 0) { y = y-2; } else { y = y+2; }
        return (y / 15) * 15;
    }

    private final Color bgLight = new Color(80,80,80);
    private final Color bgDark = new Color(40,40,40);
    private final Color bgVeryDark = new Color(30,30,30);

    private boolean inBox(int i, int j, int x, int y, int w, int h) {
        return (x <= i && i < x+w && y <= j && j < y+h);
    }

    public Color cell(int i, int j) {
        if (inBox(i,j,0,-2,5,5)) { return new Color(120,20,20); }       // e in
        if (inBox(i,j,0+150,-2,5,5)) { return new Color(120,20,20); }   // e out
        if (inBox(i,j,145,1,5,5)) { return new Color(120,20,20); }      // w in
        if (inBox(i,j,145-150,1,5,5)) { return new Color(120,20,20); }  // w out
        if (inBox(i,j,71,75,5,17)) { return new Color(120,20,20); }     // n in
        if (inBox(i,j,71,75-150,5,17)) { return new Color(120,20,20); } // n out
        if (inBox(i,j,74,62-150,5,14)) { return new Color(20,120,20); } // s in
        if (inBox(i,j,74,62,5,14)) { return new Color(20,120,20); }     // s out
        if (isGatePos(i,j)) {
            return bgLight;
        }
        if (i < 0) { return Color.BLACK; }
        if (j > 75) { return Color.BLACK; }
        if (j < -75) { return Color.BLACK; }
        if (i > 150) { return Color.BLACK; }
        if (i == 0 || j == 0) {
            return bgVeryDark;
        }
        return bgDark;
    }

}
