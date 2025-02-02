import java.util.*;

public class Point2D implements Comparable<Point2D> {

    private int x;
    private int y;

    public Point2D(int x, int y) {
        this.x = x;
        this.y = y;
    }

    public int getX() { return x; }
    public int getY() { return y; }

    public int hashCode() {
        return x + 2000*y;
    }

    public boolean equals(Object o) {
        if (o == null) { return false; }
        if (!(o instanceof Point2D)) { return false; }
        Point2D d = (Point2D)o;
        return x == d.x && y == d.y;
    }

    public String toString() {
        return "(" + x + "," + y + ")";
    }

    public int compareTo(Point2D other) {
        if (other == null) { return -1; }
        if (this.x != other.x) { return this.x - other.x; }
        return this.y - other.y;
    }

}
