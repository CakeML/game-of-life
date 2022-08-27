import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

public class Grid2DBackground implements GridModel {

    private boolean isGatePos(int i, int j) {
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
