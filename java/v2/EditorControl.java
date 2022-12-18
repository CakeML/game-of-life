import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import java.nio.file.*;

public class EditorControl extends JFrame implements GridModel, GridViewListener {

    private JLabel status = new JLabel();
    private EditorModel model;
    private GridView w;

    private boolean mouseInWindow = false;
    private int mouseX = -1000;
    private int mouseY = -1000;
    private EditorMode mode = EditorMode.SET_00;

    private enum EditorMode {
        NONE, SET_00, GATE_IN, GATE_OUT
    }

    public EditorControl(String name,String input) {
        super(name);
        setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        setSize(1100,750); setLocation(50,20);
        model = new EditorModel(name,input);
        JPanel p = new JPanel(new BorderLayout());
        w = new GridView(this,this);
        p.add(w,BorderLayout.CENTER);
        JPanel buttons = new JPanel();
        JButton set = new JButton("set (0,0)");
        set.addActionListener((ActionEvent e) -> {
                mode = EditorMode.SET_00;
            });
        buttons.add(set);
        JButton zoomIn = new JButton("zoom in");
        zoomIn.addActionListener((ActionEvent e) -> { w.zoomIn(); });
        buttons.add(zoomIn);
        JButton zoomOut = new JButton("zoom out");
        zoomOut.addActionListener((ActionEvent e) -> { w.zoomOut(); });
        buttons.add(zoomOut);
        JButton gateIn = new JButton("gate in");
        gateIn.addActionListener((ActionEvent e) -> {
                mode = EditorMode.GATE_IN;
            });
        buttons.add(gateIn);
        JButton gateOut = new JButton("gate out");
        gateOut.addActionListener((ActionEvent e) -> {
                mode = EditorMode.GATE_OUT;
            });
        buttons.add(gateOut);
        JButton run60button = new JButton("run 60 steps");
        run60button.addActionListener((ActionEvent e) -> { run60(run60button); });
        buttons.add(run60button);
        JButton fastforward = new JButton("fast forward");
        fastforward.addActionListener((ActionEvent e) -> { fast60(); });
        buttons.add(fastforward);
        JButton rename = new JButton("rename");
        rename.addActionListener((ActionEvent e) -> { model.rename(); w.repaint(); });
        buttons.add(rename);
        JButton export = new JButton("export");
        export.addActionListener((ActionEvent e) -> { export(); });
        buttons.add(export);
        p.add(buttons,BorderLayout.NORTH);
        p.add(status,BorderLayout.SOUTH);
        add(p);
        setVisible(true);
        setStatus("");
    }

    public void fast60() {
        model.startSim();
        for (int i=0;i<60;i++) {
            model.tick();
        }
        repaint();
    }

    public void run60(JButton b) {
        b.setEnabled(false);
        model.startSim();
        repaint();
        javax.swing.Timer t = new javax.swing.Timer(10,null);
        ActionListener al = new ActionListener() {
                int k = 0;
                public void actionPerformed(ActionEvent evt) {
                    k++;
                    setStatus("After tick: " + k);
                    model.tick();
                    repaint();
                    if (k >= 60) {
                        t.stop();
                        b.setEnabled(true);
                    }
                }
            };
        t.addActionListener(al);
        t.start();
    }

    public void export() {
        System.out.println("export() not implemented yet");
    }

    public static void main(String[] args) {
        String input = "!";
        String name = "";
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
            name = args[0];
        }
        EditorControl f = new EditorControl(name,input);
    }

    private void setStatus(String s) {
        status.setText("  " + s);
    }

    private final Color highlightColor = new Color(200,200,255);

    public Color cell(int i, int j) {
        if (mouseInWindow && mode == EditorMode.SET_00) {
            if (mouseX == i+2 && mouseY <= j + 2 && mouseY >= j-2) {
                return highlightColor;
            }
            if (mouseX == i-2 && mouseY <= j + 2 && mouseY >= j-2) {
                return highlightColor;
            }
            if (mouseY == j+2 && mouseX <= i + 2 && mouseX >= i-2) {
                return highlightColor;
            }
            if (mouseY == j-2 && mouseX <= i + 2 && mouseX >= i-2) {
                return highlightColor;
            }
        }
        return model.cell(i,j);
    }

    public void mouseClicked(int x, int y) {
        if (mode == EditorMode.SET_00) {
            model.translate(-x,-y);
            w.repaint();
            mode = EditorMode.NONE;
        } else if (mode == EditorMode.GATE_IN) {
            if (model.gateClick(x,y,true)) { w.repaint(); }
        } else if (mode == EditorMode.GATE_OUT) {
            if (model.gateClick(x,y,false)) { w.repaint(); }
        }
    }

    public void mouseMoved(int x, int y) {
        mouseX = x;
        mouseY = y;
        w.repaint();
        setStatus("("+x+","+y+"): " + model.cellInfo(x,y));
    }

    public void mouseExited() {
        mouseInWindow = false;
        w.repaint();
    }

    public void mouseEntered() {
        mouseInWindow = true;
        w.repaint();
    }

}
