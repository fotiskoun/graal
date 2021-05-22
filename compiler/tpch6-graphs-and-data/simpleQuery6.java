import java.io.File;
import java.io.FileNotFoundException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Random;
import java.util.Scanner;

class simpleQuery6 {
  public static void main(String[] args) throws FileNotFoundException, ParseException, InterruptedException {
    File f = new File("./tpch6SortedLineitemDQSE70MB.tbl");
    Scanner scnr = new Scanner(f);
    int rowsOftext = 600572;
    int[] discount = new int[rowsOftext];

    int i = 0;
    while (scnr.hasNextLine() && i < rowsOftext) {
      String line = scnr.nextLine();
      String[] r = line.split("\\|");

      discount[i] = (int) (Float.parseFloat(r[6]) * 100);


      i++;
    }

    //filling the arrays before the loop iteration
    //throwing out the cache clearance loop

    for (; ; ) {
      loopIteration(discount);
    }
  }

  public static void loopIteration(int[] discount) {
    int[] compressedRun = new int[discount.length];
    int[] startPosition = new int[discount.length];
    int compRaw = 1;
    compressedRun[0] = discount[0];
    startPosition[0] = 0;
    for (int r = 1; r < discount.length; r++) {
      if(discount[r] != discount[r-1]){
        compressedRun[compRaw] = discount[r];
        startPosition[compRaw] = r;
        compRaw++;
      }
    }
    startPosition[compRaw] = discount.length;	//to grab the end position
    int size = compRaw-1;

    long sum = 0;
    for (int i = 0; i <= size; i++) {
//    for (int i = 0; i < discount.length; i++) {

       if (compressedRun[i] <= 7){
//      if (discount[i] <= 7) {
      	      sum += compressedRun[i] * (startPosition[i+1] - startPosition[i]);
//              sum +=  discount[i];
      }
    }

    //1529278
    System.out.println("reve " + sum);

  }
}
