import java.io.File;
import java.io.FileNotFoundException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.Random;
import java.util.concurrent.TimeUnit;

class tpchQuery6Version {

    static class CompressedProxy {

        public int[] compressedArray;
        public int length;
        public int[] startPosition;
        public int size;

        public CompressedProxy(int[] array) {
            this.length = array.length;
            int[] cArr = new int[16];
            int[] startPos = new int[16];
            int comp_i = 0;

            cArr[0] = array[0];
            startPos[0] = 0;

            for (int i = 0; i < length; i++) {
                if (array[i] != cArr[comp_i]) {
                    comp_i++;

                    // ensure capacity
                    if (cArr.length - 1 < comp_i) {
                        cArr = Arrays.copyOf(cArr, cArr.length * 2);
                        startPos = Arrays.copyOf(startPos, startPos.length * 2);
                    }
                    cArr[comp_i] = array[i];
                    startPos[comp_i] = i;
                }
            }
            this.size = comp_i + 1;

            // ensure capacity
            if (startPos.length - 1 < comp_i + 1) {
                startPos = Arrays.copyOf(startPos, startPos.length * 2);
            }
            startPos[comp_i + 1] = this.length;
            this.compressedArray = Arrays.copyOf(cArr, comp_i + 1);
            // making the startPosition array one position larger to calculate the
            // run*length
            this.startPosition = Arrays.copyOf(startPos, comp_i + 2);
        }

        int get(int index) {
            if (this.size == 1)
                return this.compressedArray[0];

            // binry search
            int left = 0;
            int right = this.size;
            while (true) {
                if (left == right - 1) {
                    return this.compressedArray[this.size - 1];
                }
                int compIndex = (right + left) / 2;
                if (index >= this.startPosition[compIndex - 1] && index < this.startPosition[compIndex]) {
                    return this.compressedArray[compIndex - 1];
                } else if (index < this.startPosition[compIndex - 1]) {
                    right = compIndex;
                } else if (index >= this.startPosition[compIndex]) {
                    left = compIndex;
                }
            }
        }

        @Override
        public String toString() {
            return Arrays.toString(this.compressedArray) + Arrays.toString(this.startPosition);
        }
    }

    static int[][] getNextAlignment(CompressedProxy[] columns, int[] currentIterators) {
        int[][] returnAr = new int[2][];
        int colLength = columns.length;
        returnAr[0] = new int[colLength * 2];
        returnAr[1] = new int[colLength];
        int minIterator = -1;
        ArrayList<Integer> nonEndColIndexes = new ArrayList<>();

        for (int i = 0; i < colLength; i++) {
            if (currentIterators[i] != columns[i].size - 1) {
                nonEndColIndexes.add(i);
                if (columns[i].startPosition[currentIterators[i] + 1] < minIterator || minIterator < 0) {
                    minIterator = columns[i].startPosition[currentIterators[i] + 1];
                }
            }
        }

        for (int i = 0; i < colLength; i++) {
            if (nonEndColIndexes.contains(i) && columns[i].startPosition[currentIterators[i] + 1] == minIterator) {
                returnAr[0][i * 2] = columns[i].compressedArray[currentIterators[i] + 1];
                returnAr[0][i * 2 + 1] = columns[i].startPosition[currentIterators[i] + 1];
                returnAr[1][i] = currentIterators[i] + 1;
            } else {
                returnAr[0][i * 2] = columns[i].compressedArray[currentIterators[i]];
                returnAr[0][i * 2 + 1] = minIterator;
                returnAr[1][i] = currentIterators[i];
            }
        }

        return returnAr;

    }

    public static void main(String[] args) throws FileNotFoundException, ParseException, InterruptedException {
        File f = new File("./tpch6Accepted.tbl");
        Scanner scnr = new Scanner(f);
        int i = 0;
        int rowsOftext = 113860; //6001215; //600037902;
        int[] extendedprice = new int[rowsOftext];
        int[] quantity = new int[rowsOftext];
        int[] discount = new int[rowsOftext];
        int[] shipdate = new int[rowsOftext];
        SimpleDateFormat formatter = new SimpleDateFormat("yyyy-MM-dd");
//        System.out.println(scnr.nextLine());

        System.out.println("Load arrays");
        while (scnr.hasNextLine()) {//} && i < 50) {
            String line = scnr.nextLine();
            String[] r = line.split("\\|");

            extendedprice[i] = (int) (Float.parseFloat(r[5]) * 100);
            quantity[i] = (int) Float.parseFloat(r[4]);
            discount[i] = (int) (Float.parseFloat(r[6]) * 100);
            shipdate[i] = (int) (formatter.parse(r[10]).getTime() / 1000);

            i++;
        }
        scnr.close();

        System.out.println("Fill the dump Array");
        int cacheSizeIntegers = 2_500_000;
        int[] dumpArray = new int[cacheSizeIntegers];
        Random randNum = new Random();
        for (int dump = 0; dump < cacheSizeIntegers; dump++) {
            dumpArray[dump] = randNum.nextInt();
        }


        System.out.println("iterate values");

        // iterate though the arrays to create the select values

        int endDate = (int) (formatter.parse("1995-01-01").getTime() / 1000);
        int startDate = (int) (formatter.parse("1994-01-01").getTime() / 1000);

        CompressedProxy sh = new CompressedProxy(shipdate);
        // CompressedProxy ex = new CompressedProxy(extendedprice);
        CompressedProxy qu = new CompressedProxy(quantity);
        CompressedProxy di = new CompressedProxy(discount);

        // System.out.println(di.size); // 11
        // System.out.println(qu.size); // 550
        // System.out.println(sh.size); // 1347244
        // System.out.println(ex.size); // 6000557
        TimeUnit.SECONDS.sleep(1);

        for(;;) {
            callFunction(cacheSizeIntegers, dumpArray, i, di, qu, shipdate, discount, quantity, extendedprice, endDate, startDate);
        }

//        for (int iteration = 0; iteration < 15; iteration++) {
//            long start = System.nanoTime();
//
//            CompressedProxy[] cols = new CompressedProxy[]{di, qu};
//            int[] iters = new int[]{0, 0};
//            int[] curRes = new int[]{di.get(0), 0, qu.get(0), 0};
//            int[][] nextRes;
//            int length, inner_i;
//
//            long sum = 0;
//            for (i = 0; i < shipdate.length; i++) {
//                if (shipdate[i] <= endDate) {
//                    if (shipdate[i] > startDate) {
//                        if (discount[i] <= 7) {
//                            if (discount[i] >= 5) {
//                                if (quantity[i] < 24) {
//                                    sum += (extendedprice[i] * discount[i]);
//                                }
//                            }
//                        }
//                    }
//                }
//            }
//
//            // System.out.println(i + " " + j + " " + (i - j));
//            // 6001215 5887026 114189
//            System.out.println("reve");
//            System.out.println(sum);
//            // 1.23176432E12 float or 1231767619627 long
//
//            long elapsedTime = System.nanoTime() - start;
//            System.out.println((elapsedTime / 1000000) + "  milliseconds");
//
//        }
//
//        for (int flushIter = 0; flushIter < 5; flushIter++) {
//            for (int flush = 0; flush < cacheSizeIntegers; flush++) {
//                int el = dumpArray[flush];
//            }
//        }

    }
    public static void GorillaTimestamp(){

    }


    public static void callFunction(int cacheSizeIntegers, int[] dumpArray, int i, CompressedProxy di, CompressedProxy qu, int[] shipdate, int[] discount, int[] quantity,
                                    int[] extendedprice, int endDate, int startDate) {
        for (int iteration = 0; iteration < 15; iteration++) {
            long start = System.nanoTime();

            CompressedProxy[] cols = new CompressedProxy[]{di, qu};
            int[] iters = new int[]{0, 0};
            int[] curRes = new int[]{di.get(0), 0, qu.get(0), 0};
            int[][] nextRes;
            int length, inner_i;

            long sum = 0;
            for (i = 0; i < shipdate.length; i++) {
                if (shipdate[i] <= endDate) {
                    if (shipdate[i] > startDate) {
                        if (discount[i] <= 7) {
                            if (discount[i] >= 5) {
                                if (quantity[i] < 24) {
                                    sum += (extendedprice[i] * discount[i]);
                                    sum += invokeBuild();
                                }
                            }
                        }
                    }
                }
            }

            // System.out.println(i + " " + j + " " + (i - j));
            // 6001215 5887026 114189
            System.out.println("reve");
            System.out.println(sum);
            // 1.23176432E12 float or 1231767619627 long

            long elapsedTime = System.nanoTime() - start;
            System.out.println((elapsedTime / 1000000) + "  milliseconds");

        }

        for (int flushIter = 0; flushIter < 5; flushIter++) {
            for (int flush = 0; flush < cacheSizeIntegers; flush++) {
                int el = dumpArray[flush];
            }
        }
    }
    
    public static int invokeBuild(){
    	int x = 1;
    	for(int i = 0; i < 10; i ++) {
    		x+=1;
    	}
    	return x;
    }
}
/*
 * select sum(l_extendedprice * l_discount) as revenue from lineitem where
 * l_shipdate >= date '1994-01-01' and l_shipdate < date '1995-01-01' and
 * l_discount between 0.06 - 0.01 and 0.06 + 0.01 and l_quantity < 24
 *
 * 0 => ORDERKEY 1 => PARTKEY 2 => SUPPKEY 3 => LINENUMBER 4 => QUANTITY 5 =>
 * EXTENDEDPRICE 6 => DISCOUNT 7 => TAX 8 => RETURNFLAG 9 => LINESTATUS 10 =>
 * SHIPDATE 11 => COMMITDATE 12 => RECEIPTDATE 13 => SHIPINSTRUCT 14 => SHIPMODE
 * 15 => COMMENT
 */
