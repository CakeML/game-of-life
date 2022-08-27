import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

public class EditorModel implements GridModel {

    private GOLState golState;
    private Grid2DBackground bg;

    public EditorModel(String rle) {
        golState = new GOLState();
        bg = new Grid2DBackground();
    }

    public Color cell(int x, int y) {
        BoolExp b = cell(int x, int y);
        if (b instanceof BoolFalse) {
            return bg.cell(x,y);
        } else {
            return Color.WHITE;
        }
    }

}
