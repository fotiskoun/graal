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
    int rowsOftext = 600572;
    int[] discount = new int[rowsOftext];
    int[] quantity = new int[rowsOftext];

    int i = 0;
    while (scnr.hasNextLine() && i < rowsOftext) {
      String line = scnr.nextLine();
      String[] r = line.split("\\|");

      discount[i] = (int) (Float.parseFloat(r[6]) * 100);
      quantity[i] = (int) Float.parseFloat(r[4]);

      i++;
    }

    //filling the arrays before the loop iteration
    //throwing out the cache clearance loop

    for (; ; ) {
      loopIteration(discount, quantity);
    }
  }

  public static void declareToBeCompressedArrays(int[]... arrays) {
  }

  public static void loopIteration(int[] discount, int[] quantity) {
    declareToBeCompressedArrays(quantity, discount);

    long sum =0;
    for (int i = 0; i < discount.length; i++) {
//      if (quantity[i] <= 24) {
        if (discount[i] <= 7) {
          if (discount[i] >= 5) {
            sum += discount[i];
//          }
        }
      }
    }

    //1529278
    System.out.println("reve " + sum);

  }
}
