import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

public class EditorModel implements GridModel {

    private GOLState golState;
    private Grid2DBackground bg;

    public EditorModel(String str) {
        golState = new GOLState();
        bg = new Grid2DBackground();
    }

    public Color cell(int x, int y) {
        return bg.cell(x,y);
    }

}
