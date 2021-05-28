import java.io.File;
import java.io.FileNotFoundException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Random;
import java.util.Scanner;

class compressedSimpleQuery6 {
  public static void main(String[] args) throws FileNotFoundException, ParseException, InterruptedException {
    File f = new File("./tpch6SortedLineitemDQSE70MB.tbl");
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

    long sum = 0;
    // iterators to show in the startPosition arrays
    int quanIterPointer = 0;
    int discIterPointer = 0;
    // the current values from the compressed arrays
    int currentQuantity = compressedQuanRun[0];
    int currentDiscount = compressedDisRun[0];
    //the next value from the compressed arrays
    int nextQuantity = compressedQuanRun[0];
    int nextDiscount = compressedDisRun[0];
    // keep the last iterator
    int iteratorPointer = 0;
    // the next minimum iterator between the arrays
    int minNextIterator = -1;
    int length;

    for (int i = 0; i < discount.length;) {
      boolean hasFinishedQuantity = true;
      boolean hasFinishedDiscount = true;
      if (quanIterPointer != startQuanPosition.length - 1) {
        hasFinishedQuantity = false;
        minNextIterator = startQuanPosition[quanIterPointer + 1];
      }
      if (discIterPointer != startDisPosition.length - 1) {
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
