import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

public class GridView extends JPanel implements MouseListener, MouseMotionListener {

    private GridModel m;
    private GridViewListener l;

    private int cellWidth = 4;
    private int navX = -75 * cellWidth;
    private int navY = 0;

    private int mouseDownX;
    private int mouseDownY;
    private int dragX = 0;
    private int dragY = 0;

    private String displayTextString = null;
    private int displayTextX = 0;
    private int displayTextY = 0;

    public GridView(GridModel m, GridViewListener l) {
        this.m = m;
        this.l = l;
        this.addMouseListener(this);
        this.addMouseMotionListener(this);
        Font font = getFont();
        font = new Font(font.getName(), Font.PLAIN, font.getSize()+20);
        this.setFont(font);

    }

    public void paintComponent(Graphics g) {
        int w = getWidth();
        int h = getHeight();
        int midX = w/2 - cellWidth/2;
        int midY = h/2 - cellWidth/2;
        int minI = getXOnGrid(0)-1;
        int minJ = getYOnGrid(0)-1;
        int maxI = getXOnGrid(w)+1;
        int maxJ = getYOnGrid(h)+1;
        for (int i = minI; i < maxI; i++) {
            for (int j = minJ; j < maxJ; j++) {
                g.setColor(m.cell(i,j));
                g.fillRect(dragX + navX + midX + i * cellWidth,
                           dragY + navY + midY + j * cellWidth,
                           cellWidth,cellWidth);
                g.setColor(Color.BLACK);
                g.drawRect(dragX + navX + midX + i * cellWidth,
                           dragY + navY + midY + j * cellWidth,
                           cellWidth,cellWidth);
            }
        }
        if (displayTextString != null) {
            int x = dragX + navX + midX + displayTextX * cellWidth;
            int y = dragY + navY + midY + displayTextY * cellWidth;
            String text = displayTextString;
            int newWidth = this.getFontMetrics(g.getFont()).stringWidth(text);
            int newHeight = g.getFont().getSize() - 10;
            g.setColor(Color.BLACK);
            g.fillRect(x-10-2,y+23-2,newWidth+20+4,newHeight+20+4);
            g.setColor(Color.WHITE);
            g.fillRect(x-10,y+23,newWidth+20,newHeight+20);
            g.setColor(Color.BLACK);
            g.drawString(text,x-10+10,y+23+10+newHeight);
        }
    }

    public void clearDisplayText() {
        displayTextString = null;
    }

    public void setDisplayText(int x, int y, String s) {
        displayTextX = x;
        displayTextY = y;
        displayTextString = s;
    }

    // div but with truncating towards negative infinity for negative i
    private int div_neg_inf(int i, int j) {
        if (i < 0) {
            return (i - (j - 1)) / j;
        }
        return i / j;
    }

    private int getXOnGrid(int x) {
        int w = getWidth();
        int midX = w/2 - cellWidth/2;
        return div_neg_inf(x - (dragX + navX + midX), cellWidth);
    }

    private int getYOnGrid(int y) {
        int h = getHeight();
        int midY = h/2 - cellWidth/2;
        return div_neg_inf(y - (dragY + navY + midY), cellWidth);
    }

    public void mouseClicked(MouseEvent e) {
        l.mouseClicked(getXOnGrid(e.getX()),getYOnGrid(e.getY()));
    }

    public void mouseMoved(MouseEvent e) {
        l.mouseMoved(getXOnGrid(e.getX()),getYOnGrid(e.getY()));
    }

    public void mouseEntered(MouseEvent e) {
        l.mouseEntered();
    }

    public void mouseExited(MouseEvent e) {
        l.mouseExited();
    }

    public void mousePressed(MouseEvent e) {
        mouseDownX = e.getX();
        mouseDownY = e.getY();
    }

    public void mouseReleased(MouseEvent e) {
        int x = e.getX();
        int y = e.getY();
        navX += dragX;
        navY += dragY;
        dragX = 0;
        dragY = 0;
        repaint();
    }

    public void mouseDragged(MouseEvent e) {
        int x = e.getX();
        int y = e.getY();
        dragX = (x - mouseDownX);
        dragY = (y - mouseDownY);
        repaint();
    }

    public void zoomOut() {
        if (3 < cellWidth) {
            cellWidth = cellWidth - 1;
            repaint();
        }
    }

    public void zoomIn() {
        cellWidth = cellWidth + 1;
        repaint();
    }

}
