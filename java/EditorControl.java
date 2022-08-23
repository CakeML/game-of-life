import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

public class EditorControl extends JFrame implements GridModel, GridViewListener {

    public EditorControl() {
        setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        setSize(200,200); setLocation(50,50);
        GridView w = new GridView(this,this);
        add(w);
        setVisible(true);
    }

    public static void main(String[] args) {
        EditorControl f = new EditorControl();
    }

    public Color cell(int i, int j) {
        if (i == 0 && j == 0) { return Color.RED; }
        if (i == 1 && j == 1) { return Color.BLUE; }
        if (i == 1 && j == 2) { return Color.BLUE; }
        return Color.BLACK;
    }

    public void mouseClicked(int x, int y) {
        System.out.println("Clicked: x=" + x + " y=" + y);
    }

    public void mouseMoved(int x, int y) {
        System.out.println("Moved: x=" + x + " y=" + y);
    }

    public void mouseExited() {
        System.out.println("Exited.");
    }

    public void mouseEntered() {
        System.out.println("Entered.");
    }

}
