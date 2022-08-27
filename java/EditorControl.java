import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import java.nio.file.*;

public class EditorControl extends JFrame implements GridModel, GridViewListener {

    private JLabel status = new JLabel();

    public EditorControl() {
        setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        setSize(900,700); setLocation(50,50);
        JPanel p = new JPanel(new BorderLayout());
        GridView w = new GridView(this,this);
        p.add(w,BorderLayout.CENTER);
        JPanel buttons = new JPanel();
        JButton set = new JButton("set (0,0)");
        set.addActionListener((ActionEvent e) -> { set00(); });
        buttons.add(set);
        JButton zoomIn = new JButton("zoom in");
        zoomIn.addActionListener((ActionEvent e) -> { w.zoomIn(); });
        buttons.add(zoomIn);
        JButton zoomOut = new JButton("zoom out");
        zoomOut.addActionListener((ActionEvent e) -> { w.zoomOut(); });
        buttons.add(zoomOut);
        JButton gateIn = new JButton("gate in");
        gateIn.addActionListener((ActionEvent e) -> { gateIn(); });
        buttons.add(gateIn);
        JButton gateOut = new JButton("gate out");
        gateOut.addActionListener((ActionEvent e) -> { gateOut(); });
        buttons.add(gateOut);
        JButton run60 = new JButton("run 60 steps");
        run60.addActionListener((ActionEvent e) -> { run60(); });
        buttons.add(run60);
        JButton export = new JButton("export");
        export.addActionListener((ActionEvent e) -> { export(); });
        buttons.add(export);
        p.add(buttons,BorderLayout.NORTH);
        p.add(status,BorderLayout.SOUTH);
        add(p);
        setVisible(true);
        setStatus("");
    }

    public void set00() {
        System.out.println("..");
    }

    public void gateIn() {
        System.out.println("..");
    }

    public void gateOut() {
        System.out.println("..");
    }

    public void run60() {
        System.out.println("..");
    }

    public void export() {
        System.out.println("..");
    }

    public static void main(String[] args) {
        String input = "!";
        if (args.length > 0) {
            Path path = Paths.get(args[0]);
            try {
                input = new String(Files.readAllBytes(path));
                int i = 0;
                while (i<input.length() && input.charAt(i) != '\n') {
                    i++;
                }
                if (i<input.length()) {
                    input = input.substring(i+1);
                }
            } catch (Exception e) {}
        }
        System.out.println(input);
        EditorControl f = new EditorControl();
    }

    private void setStatus(String s) {
        status.setText("  " + s);
    }

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
        if (i == 0 && j == 0) { return Color.RED; }
        if (i == 1 && j == 1) { return Color.GREEN; }
        if (i == 1 && j == 2) { return Color.YELLOW; }
        if (i == 1 && j == 3) { return Color.WHITE; }
        if (isGatePos(i,j)) {
            return bgLight;
        }
        if (i == 0 || j == 0) {
            return bgVeryDark;
        }
        return bgDark;
    }

    public void mouseClicked(int x, int y) {
        setStatus("Clicked: x=" + x + " y=" + y);
    }

    public void mouseMoved(int x, int y) {
        setStatus("Moved: x=" + x + " y=" + y);
    }

    public void mouseExited() {
        setStatus("Exited.");
    }

    public void mouseEntered() {
        setStatus("Entered.");
    }



}
