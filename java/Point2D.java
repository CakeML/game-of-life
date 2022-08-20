public class Point2D {

    private int x;
    private int y;

    public Point2D(int x, int y) {
        this.x = x;
        this.y = y;
    }

    public int x() { return x; }
    public int y() { return y; }

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

}
