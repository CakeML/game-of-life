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

    private final Color bgLighter = new Color(120,120,120);
    private final Color bgLight = new Color(80,80,80);
    private final Color bgDark = new Color(40,40,40);
    private final Color bgVeryDark = new Color(30,30,30);
    private final Color bgDarkBlue = new Color(20,20,120);

    private boolean inBox(int i, int j, int x, int y, int w, int h) {
        return (x <= i && i < x+w && y <= j && j < y+h);
    }

    public Color cell(int i, int j) {
        //if (inBox(i,j,-1,-3,7,7)) { return bgDarkBlue; }       // e in
        if (inBox(i,j,-1+150,-3,7,7)) { return bgDarkBlue; }   // e out
        //if (inBox(i,j,144,0,7,7)) { return bgDarkBlue; }      // w in
        if (inBox(i,j,144-150,0,7,7)) { return bgDarkBlue; }  // w out
        //if (inBox(i,j,70,75,7,18)) { return bgDarkBlue; }     // n in
        if (inBox(i,j,70,75-150+11,7,7)) { return bgDarkBlue; } // n out
        //if (inBox(i,j,73,61-150,7,16)) { return bgDarkBlue; } // s in
        if (inBox(i,j,73,61,7,7)) { return bgDarkBlue; }     // s out
        if (-38 < i && i < 188 && -113 < j && j < 113) {
            if ((i + 75/2 + 750) % 75 == 74) { return bgVeryDark; }
            if ((i + 75/2 + 750) % 75 == 0 ) { return bgVeryDark; }
            if ((j + 75/2 + 750) % 75 == 74) { return bgVeryDark; }
            if ((j + 75/2 + 750) % 75 == 0 ) { return bgVeryDark; }
        }
        /* if (isGatePos(i,j)) {
            return bgLight;
        } */
        if (i <= 0) { return Color.BLACK; }
        if (j > 75) { return Color.BLACK; }
        if (j <= -75) { return Color.BLACK; }
        if (i > 150) { return Color.BLACK; }
        return bgDark;
    }

    public static void main(String[] args) {
        Grid2DBackground bg = new Grid2DBackground();
        int xd = 75;
        int yd = 150;
        for (int j=-112+yd; j<-112+75+yd; j++) {
            for (int i=-37+xd; i<-37+75+xd; i++) {
                String s = "s";
                if (bg.cell(i,j).equals(bg.bgVeryDark)) {
                    s = "?";
                }
                if (bg.cell(i,j).equals(bg.bgDark)) {
                    s = "s";
                }
                if (bg.cell(i,j).equals(bg.bgDarkBlue)) {
                    s = ".";
                }
                if (bg.cell(i,j).equals(Color.BLACK)) {
                    s = "r";
                }
                System.out.print(s);
            }
            System.out.println();
        }
    }

}
