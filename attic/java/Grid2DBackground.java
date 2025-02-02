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

    public Color cell(int i, int j) {
        if (isGatePos(i,j)) {
            return bgLight;
        }
        if (i == 0 || j == 0) {
            return bgVeryDark;
        }
        return bgDark;
    }

}
