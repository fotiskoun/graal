import java.io.File;
import java.io.FileNotFoundException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Random;
import java.util.Scanner;

class simpleQuery6 {
  public static void main(String[] args) throws FileNotFoundException, ParseException, InterruptedException {
    File f = new File("./tpch6Accepted.tbl");
    Scanner scnr = new Scanner(f);
    int rowsOftext = 113860;
    int[] discount = new int[rowsOftext];
    int[] quantity = new int[rowsOftext];
    int[] shipdate = new int[rowsOftext];
    SimpleDateFormat formatter = new SimpleDateFormat("yyyy-MM-dd");

    int i = 0;
    while (scnr.hasNextLine() && i < rowsOftext) {
      String line = scnr.nextLine();
      String[] r = line.split("\\|");

      discount[i] = (int) (Float.parseFloat(r[6]) * 100);
      quantity[i] = (int) Float.parseFloat(r[4]);
      shipdate[i] = (int) (formatter.parse(r[10]).getTime() / 1000);

      i++;
    }

    //filling the arrays before the loop iteration
    //throwing out the cache clearance loop

    int startDate = (int) (formatter.parse("1994-01-01").getTime() / 1000);
    int endDate = (int) (formatter.parse("1995-01-01").getTime() / 1000);

    for (; ; ) {
      loopIteration(discount, quantity, shipdate, startDate, endDate);
    }
  }

  public static void declareToBeCompressedArrays(int[]... arrays) {
  }

  public static void loopIteration(int[] discount, int[] quantity, int[] shipdate, int startDate, int endDate) {
    declareToBeCompressedArrays(quantity, discount);

    long sum = 0;
    long start = System.nanoTime();
    for (int iter = 0; iter < 50; iter++) {
      sum = 0;
      for (int i = 0; i < discount.length; i++) {
        if (quantity[i] <= 24) {
          if (discount[i] <= 7) {
            if (discount[i] >= 5) {
              if(shipdate[i] <= endDate){
                if(shipdate[i] > startDate) {
                  sum += discount[i];
                }
              }
            }
          }
        }
      }
    }
    long elapsedTime = System.nanoTime() - start;
    System.out.println((elapsedTime / 1000000) + "  milliseconds");
    //1529278
    System.out.println("reve " + sum);

  }
}
