import java.io.File;
import java.io.FileNotFoundException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Random;
import java.util.Scanner;

class compressedSimpleQuery6 {
  public static void main(String[] args) throws FileNotFoundException, ParseException, InterruptedException {
    File f = new File("./tpch6Accepted.tbl");/*tpch6Accepted*//*tpch6SortedLineitemDQSE70MB*/
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

    //compress quantity Array
    int[] compressedQuanRun = new int[quantity.length];
    int[] startQuanPosition = new int[quantity.length];
    int compQuanRaw = 1;
    compressedQuanRun[0] = quantity[0];
    startQuanPosition[0] = 0;
    for (int r = 1; r < quantity.length; r++) {
      if (quantity[r] != quantity[r - 1]) {
        compressedQuanRun[compQuanRaw] = quantity[r];
        startQuanPosition[compQuanRaw] = r;
        compQuanRaw++;
      }
    }
    startQuanPosition[compQuanRaw] = quantity.length;  //to grab the end position

    //compress discount Array
    int[] compressedDisRun = new int[discount.length];
    int[] startDisPosition = new int[discount.length];
    int compDisRaw = 1;
    compressedDisRun[0] = discount[0];
    startDisPosition[0] = 0;
    for (int r = 1; r < discount.length; r++) {
      if (discount[r] != discount[r - 1]) {
        compressedDisRun[compDisRaw] = discount[r];
        startDisPosition[compDisRaw] = r;
        compDisRaw++;
      }
    }
    //to grab the end position
    startDisPosition[compDisRaw] = discount.length;


    long sum = 0;/*118*/
    // iterators to show in the startPosition arrays
    int quanIterPointer = 0;/*119*/
    int discIterPointer = 0;/*120*/
    // the current values from the compressed arrays
    int currentQuantity = compressedQuanRun[0];/*121*/
    int currentDiscount = compressedDisRun[0];/*122*/
    //the next value from the compressed arrays
    int nextQuantity = compressedQuanRun[0];/*123*/
    int nextDiscount = compressedDisRun[0];/*124*/
    // keep the last iterator
    int iteratorPointer = 0;/*125*/
    // the next minimum iterator between the arrays
    int length;

    /*i = 127*/
    for (int i = 0; i < discount.length;) {
      int minNextIterator = -1;/*126*/
      boolean hasFinishedQuantity = true;
      boolean hasFinishedDiscount = true;
      if (quanIterPointer != compQuanRaw) {
        hasFinishedQuantity = false;
        if (startQuanPosition[quanIterPointer + 1] < minNextIterator || minNextIterator < 0) {
          minNextIterator = startQuanPosition[quanIterPointer + 1];
        }
      }

      if (discIterPointer != compDisRaw) {
        hasFinishedDiscount = false;
        if (startDisPosition[discIterPointer + 1] < minNextIterator || minNextIterator < 0) {
          minNextIterator = startDisPosition[discIterPointer + 1];
        }
      }

      if (!hasFinishedQuantity && startQuanPosition[quanIterPointer + 1] == minNextIterator) {
        quanIterPointer++;
        nextQuantity = compressedQuanRun[quanIterPointer];
      }

      if (!hasFinishedDiscount && startDisPosition[discIterPointer + 1] == minNextIterator) {
        discIterPointer++;
        nextDiscount = compressedDisRun[discIterPointer];
      }

      if (minNextIterator == -1) {
        length = quantity.length - iteratorPointer;
      } else {
        length = minNextIterator - iteratorPointer;
      }

      if (currentQuantity <= 24) {
        if (currentDiscount <= 7) {
          if (currentDiscount >= 5) {
            sum += currentDiscount * length;
            i += length;
          } else i += length;
        } else i += length;
      } else i += length;
      currentQuantity = nextQuantity;
      currentDiscount = nextDiscount;
      iteratorPointer = minNextIterator;
    }

    //1529278
    System.out.println("reve " + sum);

  }
}
