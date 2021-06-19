import java.io.File;
import java.io.FileNotFoundException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Random;
import java.util.Scanner;

class compressedSimpleQuery6 {
  public static void main(String[] args) throws FileNotFoundException, ParseException, InterruptedException {
    File f = new File("./tpch6Accepted.tbl");/*tpch6Accepted*//*tpch6SortedLineitemDQSE70MB*/
    /*tpch6SortedLineitemDQSE*/
    Scanner scnr = new Scanner(f);
    int rowsOftext = 6001215;
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

    int startDate = (int) (formatter.parse("1994-01-01").getTime() / 1000);
    int endDate = (int) (formatter.parse("1995-01-01").getTime() / 1000);


    //filling the arrays before the loop iteration
    //throwing out the cache clearance loop

    for (; ; ) {
      loopIteration(discount, quantity, shipdate, startDate, endDate);
    }
  }

  public static void declareToBeCompressedArrays(int[]... arrays) {
  }

  public static void loopIteration(int[] discount, int[] quantity, int[] shipdate, int startDate, int endDate) {
    declareToBeCompressedArrays(quantity, discount, shipdate);

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

    long sum = 0;/*118*/
    long start = System.nanoTime();
    for (int iter = 0; iter < 50; iter++) {
      sum = 0;/*137*/
      // iterators to show in the startPosition arrays
      int quanIterPointer = 0;/*138*/
      int discIterPointer = 0;/*139*/
      // the current values from the compressed arrays
      int currentQuantity = compressedQuanRun[0];/*140*/
      int currentDiscount = compressedDisRun[0];/*141*/
      //the next value from the compressed arrays
      int nextQuantity = compressedQuanRun[0];/*142*/
      int nextDiscount = compressedDisRun[0];/*143*/
      // keep the last iterator
      int iteratorPointer = 0;/*144*/
      // the next minimum iterator between the arrays
      int minNextIterator = -1;/*145*/
      int length;


      /*i = 146*/
      for (int i = 0; i < discount.length; ) {
        boolean hasFinishedQuantity = true;
        boolean hasFinishedDiscount = true;
        if (quanIterPointer != compQuanRaw) {
          hasFinishedQuantity = false;
          minNextIterator = startQuanPosition[quanIterPointer + 1];
        }

        if (discIterPointer != compDisRaw) {
          hasFinishedDiscount = false;
          if (startDisPosition[discIterPointer + 1] < minNextIterator) {
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
          length = discount.length - iteratorPointer;
        } else {
          length = minNextIterator - iteratorPointer;
        }

        if (currentQuantity <= 24) {
          if (currentDiscount <= 7) {
            if (currentDiscount >= 5) {
              for (int inner_i = 0; inner_i < length; inner_i++) {
                if (shipdate[inner_i + i] <= endDate) {
                  if (shipdate[inner_i + i] > startDate) {
                    sum += currentDiscount;
                  }
                }
              }
              i += length;
            } else i += length;
          } else i += length;
        } else i += length;
        currentQuantity = nextQuantity;
        currentDiscount = nextDiscount;
        iteratorPointer = minNextIterator;
      }
    }

    long elapsedTime = System.nanoTime() - start;
    System.out.println((elapsedTime / 1000000) + "  milliseconds");

    //1529278
    System.out.println("reve " + sum);

  }
}
