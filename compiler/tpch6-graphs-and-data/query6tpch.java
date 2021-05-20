import java.io.File;
import java.io.FileNotFoundException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Random;
import java.util.Scanner;

class query6tpch {
  public static void main(String[] args) throws FileNotFoundException, ParseException, InterruptedException {
    File f = new File("./tpch6Accepted.tbl");
    Scanner scnr = new Scanner(f);
    int rowsOftext = 10000;
    int[] extendedprice = new int[rowsOftext];
    int[] quantity = new int[rowsOftext];
    int[] discount = new int[rowsOftext];
    int[] shipdate = new int[rowsOftext];
    SimpleDateFormat formatter = new SimpleDateFormat("yyyy-MM-dd");

    int i = 0;
    while (scnr.hasNextLine() && i < rowsOftext) {
      String line = scnr.nextLine();
      String[] r = line.split("\\|");

      extendedprice[i] = (int) (Float.parseFloat(r[5]) * 100);
      quantity[i] = (int) Float.parseFloat(r[4]);
      discount[i] = (int) (Float.parseFloat(r[6]) * 100);
      shipdate[i] = (int) (formatter.parse(r[10]).getTime() / 1000);

      i++;
    }

    //filling the arrays before the loop iteration
    //throwing out the cache clearance loop

    int endDate = (int) (formatter.parse("1995-01-01").getTime() / 1000);
    int startDate = (int) (formatter.parse("1994-01-01").getTime() / 1000);

    for (; ; ) {
      loopIteration(endDate, startDate, shipdate, discount, quantity, extendedprice);
    }
  }

  public static void loopIteration(int endDate, int startDate, int[] shipdate,
                                   int[] discount, int[] quantity, int[] extendedprice) {
//    int[] compressedRun = new int[shipdate.length];
//    int[] startPosition = new int[shipdate.length];
//    int compRaw = 1;
//    compressedRun[0] = shipdate[0];
//    startPosition[0] = 0;
//    for (int r = 1; r < shipdate.length; r++) {
//      if(shipdate[r] != shipdate[r-1]){
//        compressedRun[compRaw] = shipdate[r];
//        startPosition[compRaw] = r;
//        compRaw++;
//      }
//    }
//
//    int size = compRaw-1;

    long sum = 0;
    for (int i = 0; i < shipdate.length; i++) {
//      int shipdateVal = 0; //phi79
//      boolean foundPred = true; //phi80
//      if (size == 1)
//        shipdateVal = compressedRun[0];
//
//      // binry search
//      int left = 0; //phi81
//      int right = size; //phi82
//      while (foundPred) {
//        if (left == right - 1) {
//          shipdateVal = compressedRun[size - 1];
//          foundPred = false;
//        }
//        int compIndex = (right + left) / 2;
//        if (i >= startPosition[compIndex - 1] && i < startPosition[compIndex]) {
//          shipdateVal = compressedRun[compIndex - 1];
//          foundPred = false;
//        } else if (i < startPosition[compIndex - 1]) {
//          right = compIndex;
//        } else if (i >= startPosition[compIndex]) {
//          left = compIndex;
//        }
//      }

      if (shipdate[i] <= endDate) {//if (shipdateVal <= endDate) {
        if (shipdate[i] > startDate) {// if (shipdateVal > startDate) {
          if (discount[i] <= 7) {
            if (discount[i] >= 5) {
              if (quantity[i] < 24) {
                sum += (extendedprice[i] * discount[i]);
              }
            }
          }
        }
      }
    }

    System.out.println("reve " + sum);

  }
}