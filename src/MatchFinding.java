import com.sun.org.apache.xerces.internal.impl.xpath.regex.Match;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.lang.reflect.Array;
import java.util.*;
import java.io.*;

/**
 * Created by william on 2017-04-01.
 */
public class MatchFinding extends Parser {

    String FS1;
    String FS2;
    Parser parsedFile = new Parser();
    String[] description = parsedFile.getDescription();
    String[] sequence = parsedFile.getSequence();
    static ArrayList<indexTuple> listOfIndexes = new ArrayList<indexTuple>();
    public MatchFinding() {
        super();
    }


    //TODO: implement data structure for suffix tree

    /** Class Node **/
    static class Node {
        public int suffix_node;
        public static int Count = 1;

        /** Constructor **/
        public Node(){
            suffix_node = -1;
        }
    }

    static class indexTuple{
        private int firstIndexFirstSeq;
        private int lastIndexFirstSeq;
        private int firstIndexSecondSeq;
        private int lastIndexSecondSeq;

        public indexTuple(int firstIndex_FirstSeq, int lastIndex_FirstSeq, int firstIndex_SecondSeq, int lastIndex_SecondSeq){
            firstIndexFirstSeq = firstIndex_FirstSeq;
            lastIndexFirstSeq = lastIndex_FirstSeq;
            firstIndexSecondSeq = firstIndex_SecondSeq;
            lastIndexSecondSeq = lastIndex_SecondSeq;
        }
        public int getFirstIndexFirstSeq(){
            return firstIndexFirstSeq;
        }
        public int getLastIndexFirstSeq(){
            return lastIndexFirstSeq;
        }
        public int getFirstIndexSecondSeq(){
            return firstIndexSecondSeq;
        }
        public int getLastIndexSecondSeq(){
            return lastIndexSecondSeq;
        }

        public void setFirstIndexFirstSeq(int first){
            this.firstIndexFirstSeq = first;
        }
        public void setLastIndexFirstSeq(int last){
            this.lastIndexFirstSeq = last;
        }
        public void setFirstIndexSecondSeq(int first){
            this.firstIndexSecondSeq = first;
        }
        public void setLastIndexSecondSeq(int last){
            this.firstIndexSecondSeq = last;
        }
    }

    /** Class Suffix Tree **/
    static class SuffixTree {


        private static final int MAX_LENGTH = 50000;
        private static final int HASH_TABLE_SIZE = 50000;

        private char[] T = new char[ MAX_LENGTH ];
        private int N;
        private Edge[] Edges ;
        private Node[] Nodes ;
        private Suffix active;
        String longestString = "";
        MatchFinding MF = new MatchFinding();
        String FS1;
        String FS2;
        ArrayList<String> ListOfSubseqs = new ArrayList<>();
        /** Class Suffix **/
        class Suffix
        {
            public int origin_node;
            public int first_char_index;
            public int last_char_index;
            /** Constructor **/
            public Suffix(int node, int start, int stop ){
                origin_node = node ;
                first_char_index = start ;
                last_char_index = stop;
            }
            /** Function Implicit  **/
            public boolean Implicit(){
                return first_char_index > last_char_index;
            }
            /** Function Explicit  **/
            public boolean Explicit() {
                return first_char_index > last_char_index;
            }
            /** Function Canonize()
             * A suffix in the tree is denoted by a Suffix structure
             * that denotes its last character.  The canonical
             * representation of a suffix for this algorithm requires
             * that the origin_node by the closest node to the end
             * of the tree.  To force this to be true, we have to
             * slide down every edge in our current path until we
             * reach the final node
             **/
            public void Canonize() {
                if (!Explicit() )
                {
                    Edge edge = Find( origin_node, T[ first_char_index ] );
                    int edge_span = edge.last_char_index - edge.first_char_index;
                    while ( edge_span <= ( last_char_index - first_char_index ) ) {
                        first_char_index = first_char_index + edge_span + 1;
                        origin_node = edge.end_node;
                        if ( first_char_index <= last_char_index )
                        {
                            edge = Find( edge.end_node, T[ first_char_index ] );
                            edge_span = edge.last_char_index - edge.first_char_index;
                        }
                    }
                }
            }
        }

        /** Class Edge **/
        class Edge {
            public int first_char_index;
            public int last_char_index;
            public int end_node;
            public int start_node;
            /** Constructor **/
            public Edge()
            {
                start_node = -1;
            }
            /** Constructor **/
            public Edge( int init_first, int init_last, int parent_node )
            {
                first_char_index = init_first;
                last_char_index = init_last;
                start_node = parent_node;
                end_node = Node.Count++;
            }
            /** function Insert ()
             *  A given edge gets a copy of itself inserted into the table
             *  with this function.  It uses a linear probe technique, which
             *  means in the case of a collision, we just step forward through
             *  the table until we find the first unused slot.
             **/
            public void Insert(){
                int i = Hash( start_node, T[ first_char_index ] );
                while ( Edges[ i ].start_node != -1 )
                    i = ++i % HASH_TABLE_SIZE;
                Edges[ i ] = this;
            }
            /** function SplitEdge ()
             *  This function is called
             *  to split an edge at the point defined by the Suffix argument
             **/
            public int SplitEdge( Suffix s )
            {
                Remove();
                Edge new_edge =  new Edge( first_char_index, first_char_index + s.last_char_index - s.first_char_index, s.origin_node );
                new_edge.Insert();
                Nodes[ new_edge.end_node ].suffix_node = s.origin_node;
                first_char_index += s.last_char_index - s.first_char_index + 1;
                start_node = new_edge.end_node;
                Insert();
                return new_edge.end_node;
            }
            /** function Remove ()
             *  This function is called to remove an edge from hash table
             **/
            public void Remove()
            {
                int i = Math.abs(Hash( start_node, T[ first_char_index ] ));
                while ( Edges[ i ].start_node != start_node ||
                        Edges[ i ].first_char_index != first_char_index )
                    i = ++i % HASH_TABLE_SIZE;
                for ( ; ; )
                {
                    Edges[ i ].start_node = -1;
                    int j = i;
                    for ( ; ; )
                    {
                        i = ++i % HASH_TABLE_SIZE;
                        if ( Edges[ i ].start_node == -1 )
                            return;
                        int r = Hash( Edges[ i ].start_node, T[ Edges[ i ].first_char_index ] );
                        if ( i >= r && r > j )
                            continue;
                        if ( r > j && j > i )
                            continue;
                        if ( j > i && i >= r )
                            continue;
                        break;
                    }
                    Edges[ j ] = Edges[ i ];
                }
            }
        }



        /** Constructor */

        public SuffixTree()

        {
            Edges = new Edge[ HASH_TABLE_SIZE ];
            for (int i = 0; i < HASH_TABLE_SIZE; i++)
                Edges[i] = new Edge();
            Nodes = new Node[ MAX_LENGTH * 2 ];
            for (int i = 0; i < MAX_LENGTH * 2 ; i++)
                Nodes[i] = new Node();
            active = new Suffix( 0, 0, -1 );
        }

        /** Function Find() - function to find an edge **/
        public Edge Find( int node, int c ){
            int i = Hash( node, c );
            for ( ; ; )
            {
                if ( Edges[ i ].start_node == node )
                    if ( c == T[ Edges[ i ].first_char_index ] )
                        return Edges[ i ];
                if ( Edges[ i ].start_node == -1 )
                    return Edges[ i ];
                i = ++i % HASH_TABLE_SIZE;
            }
        }

        /** Function Hash() - edges are inserted into the hash table using this hashing function **/
        public static int Hash( int node, int c ){
            return (( node << 8 ) + c ) % HASH_TABLE_SIZE;
        }
        /** Function AddPrefix() - called repetitively, once for each of the prefixes of the input string **/
        public void AddPrefix( Suffix active, int last_char_index )
        {
            int parent_node;
            int last_parent_node = -1;
            for ( ; ; )
            {
                Edge edge;
                parent_node = active.origin_node;
                if ( active.Explicit() ){
                    edge = Find( active.origin_node, T[ last_char_index ] );
                    if ( edge.start_node != -1 )
                        break;
                }
                else{
                    edge = Find( active.origin_node, T[ active.first_char_index ] );
                    int span = active.last_char_index - active.first_char_index;
                    if ( T[ edge.first_char_index + span + 1 ] == T[ last_char_index ] )
                        break;
                    parent_node = edge.SplitEdge( active );
                }
                Edge new_edge = new Edge( last_char_index, N, parent_node );
                new_edge.Insert();
                if ( last_parent_node > 0 )
                    Nodes[ last_parent_node ].suffix_node = parent_node;
                last_parent_node = parent_node;
                if ( active.origin_node == 0 )
                    active.first_char_index++;
                else
                    active.origin_node = Nodes[ active.origin_node ].suffix_node;
                active.Canonize();
            }
            if ( last_parent_node > 0 )
                Nodes[ last_parent_node ].suffix_node = parent_node;
            active.last_char_index++;
            active.Canonize();
        }
        /** Function to print all contents and details of suffix tree **/
        public void dump_edges(int current_n ){
            System.out.println(" Start  End  Suf  First Last  String\n");
            for ( int j = 0 ; j < HASH_TABLE_SIZE ; j++ )
            {
                Edge s = Edges[j];
                if ( s.start_node == -1 )
                    continue;
                System.out.printf("%5d %5d %3d %5d %6d   ", s.start_node , s.end_node, Nodes[ s.end_node ].suffix_node, s.first_char_index, s.last_char_index);
                int top;
                if ( current_n > s.last_char_index )
                    top = s.last_char_index;
                else
                    top = current_n;
                for ( int l = s.first_char_index ; l <= top; l++)
                    System.out.print( T[ l ]);
                System.out.println();
            }
        }

        public String subSequence_2(){
            ArrayList<Edge> listofEdges = new ArrayList<Edge>();
            for (int i = 0; i < HASH_TABLE_SIZE; i++){
                Edge s = Edges[i];
                if (s.start_node == -1){
                    continue;
                }
                listofEdges.add(s);
            }
            return(subSequenceHelper(listofEdges));
//            long endTime = System.currentTimeMillis();
//            System.out.println("TIME:" + (endTime - startTime) + "ms");
        }

        public String getStringFromEdge(Edge e){
            StringBuilder sb = new StringBuilder();
            String returnString;
            for (int i = e.first_char_index; i <= e.last_char_index; i++){
                sb.append(T[i]);

            }
            returnString = sb.toString();
            return returnString;
        }

        // helper to build the tuples?
        // indexTuple class might also need a key of some sort to ensure we're accessing the right one
        // complexity is getting too high. every time we concatenate two strings with matching
        // start/end indexes, we would have to update the last_char_index
        // difficult to do this because of the way we concatenate our strings with matching start/end indexes
        // upon further thought i think we definitely need a key index of some sort

        public void buildTheTuple(Edge e){

//            indexTuple toAdd = new indexTuple(s, first, second);
//            listOfIndexes.add(toAdd);
        }

        public String followTheRabbitHole(Edge s, ArrayList<Edge> allEdges) {
            String builtString = "";
            String tempString = getStringFromEdge(s);
            int currentMax = 0;
            int longestSoFar = 0;
            ArrayList<Edge> listWithSameStartEnd = new ArrayList<Edge>();

            for (int i = 0; i < allEdges.size(); i++) {
                if (s.end_node == allEdges.get(i).start_node) {
                    listWithSameStartEnd.add(allEdges.get(i));
                }
            }
            if ((listWithSameStartEnd.size() < 2) && (Nodes[s.end_node].suffix_node != -1)){
                tempString = getStringFromEdge(s);
                if (tempString.length() > currentMax){
                    return tempString;
                }
            }
            for (int i = 0; i < listWithSameStartEnd.size(); i++){
                String tempLongestString = (findLongest(followTheRabbitHole(listWithSameStartEnd.get(i), allEdges)));
                if (FS1.contains(tempLongestString) && FS2.contains(tempLongestString)) {
                    longestString = (findLongest(followTheRabbitHole(listWithSameStartEnd.get(i), allEdges)));
                    tempString = getStringFromEdge(s).concat(longestString);
                    if (((double) tempString.length()) > ((double) (longestSoFar/2.0))){
                        longestSoFar = tempString.length();
                        ListOfSubseqs.add(tempString);
                    }
                    if (tempString.length() > builtString.length()) {
                        builtString = tempString;
                        currentMax = builtString.length();
                    }
                }
            }
            longestString = "";
            return builtString;
        }

        public String findLongest(String str){
            if (str.length() > longestString.length()){
                return str;
            }
            else return longestString;
        }

        public String subSequenceHelper(ArrayList<Edge> listOfEdges){
//            ArrayList<Edge> newList = new ArrayList<>();
//            for (Edge e : listOfEdges){
//                if (Nodes[e.end_node].suffix_node != -1){
//                    newList.add(e);
//                }
//            }
            String temp = "";
            int current = 0;
            String longestSoFar = "";
            String first = "";
            ArrayList<Edge> listWithSameStartEnd = new ArrayList<>();
            for (int i = 0; i < listOfEdges.size(); i++) {
                Edge s = listOfEdges.get(i);
                first = getStringFromEdge(s);

                temp = followTheRabbitHole(s, listOfEdges);
                if (temp.length() > longestSoFar.length()){
                    longestSoFar = temp;
                }
          listWithSameStartEnd.clear();
            }
                System.out.println(longestSoFar);

            return longestSoFar;
        }

        public void doTraversal(){
            int currentMax = 0;
            int index = 0;
            boolean extra = false;
            int remembered = 0;
            int[] toAdd = new int[Edges.length];

            for (int i = 0; i < Edges.length; i++){
                Edge e = Edges[i];

                if (Nodes[e.end_node].suffix_node == -1){
                    continue;
                }


                if ((Edges[i].last_char_index - Edges[i].first_char_index) == 0){
                       extra = true;
                       remembered = Edges[i].last_char_index;
                }
//                if ((Edges[i].last_char_index > ))

                if (Math.abs(Edges[i].last_char_index - Edges[i].first_char_index) > currentMax){
                    currentMax = Math.abs(Edges[i].last_char_index - Edges[i].first_char_index);
                    index = i;
                }
            }
            System.out.println("BREAK");
            Edge s = Edges[index];
            System.out.printf("%5d %5d %3d %5d %6d   ", s.start_node , s.end_node, Nodes[ s.end_node ].suffix_node, s.first_char_index, s.last_char_index);
            if (extra) {
                System.out.print(T[remembered]);
            }
            int top = s.last_char_index;
            for ( int l = s.first_char_index ; l <= top; l++)
                System.out.print( T[ l ]);
            System.out.println();

        }




    }
    //TODO: concatenating helper func.
        // place character 'N' between the two sequences
        // two ways of doing things?
        //      1. take string 1, concatenate N, concatenate string 2?
        //          - bad run time?
        //      2. take strings and turn them into linked list, point end of seqOne to
        //         string N, then point that to beginning of seqTwo
        //          does this have any run time improvements?
     public static String concatenateSequences(String[] seqOne, String[] seqTwo){
         int seqOneLength = seqOne.length;
         int seqTwoLength = seqTwo.length;
         int newSeqLength = seqOneLength + seqTwoLength + 1;
         int counter = 0;

         String[] combinedArray = new String[newSeqLength];
         for (int i = 0; i < seqOneLength; i++){
             combinedArray[i] = seqOne[i];
         }
         combinedArray[seqOneLength] = "N";
         for (int j = seqOneLength+1; j < newSeqLength; j++){
             combinedArray[j] = seqTwo[counter];
             counter++;
         }
         StringBuilder builder = new StringBuilder();
         for(String s : combinedArray) {
             builder.append(s);
         }
         return builder.toString();

     }

    //TODO: maximal repeated substring function
        // used once for each sequence

    //TODO: maximal matches function

    public static ArrayList<String> returnLongerStrings(ArrayList<String> listToCheck, String longestString, String seqOne, String seqTwo){

         ArrayList<String> shorterList = new ArrayList<String>();
         for (String s : listToCheck){
             if (s.length() >= Math.ceil((longestString.length()/2.0)) && !(shorterList.contains(s))){
                 if (((seqOne.contains(s) && (seqTwo.contains(s))))) {
                     shorterList.add(s);
                 }
             }
         }
         return shorterList;
    }

    public static ArrayList<String> returnNonRepeatStrings(ArrayList<String> listToCheck){
        String temp = "";
        for (int i = 0; i <= listToCheck.size()-1; i++){
            for (int j = i + 1; j <= listToCheck.size()-1; j++)
                if (listToCheck.get(j).contains(listToCheck.get(i))){
                    if (Math.abs((j - i)) > 1){
                        temp = listToCheck.get(j);
                        listToCheck.set(j, listToCheck.get(i));
                        listToCheck.set(i, temp);
                        listToCheck.remove(j);
                        j = i+1;
                    }
                    else {
                        listToCheck.remove(i);
                        j--;
                    }
            }
            else if (listToCheck.get(i).contains(listToCheck.get(j))){
                        listToCheck.remove(j);
                        j--;
                }
        }
        System.out.println(listToCheck);
        System.out.println(listToCheck.size());
        Comparator<String> x = new Comparator<String>()
        {
            @Override
            public int compare(String o1, String o2)
            {
                if(o1.length() > o2.length())
                    return -1;

                if(o2.length() > o1.length())
                    return 1;

                return 0;
            }
        };

        Collections.sort(listToCheck, x);
        System.out.println("SORTED " + listToCheck);
        return listToCheck;
    }


    public static void alignAnchors(String seqOne, String seqTwo, ArrayList<String> anchorList){
        for (int i = 0; i < anchorList.size(); i++){
            int seqOneFirst = seqOne.indexOf(anchorList.get(i));
            int seqOneLast = seqOneFirst + anchorList.get(i).length();
            int seqTwoFirst = seqTwo.indexOf(anchorList.get(i));
            int seqTwoLast = seqTwoFirst + anchorList.get(i).length();
            indexTuple indexToAdd = new indexTuple(seqOneFirst, seqOneLast, seqTwoFirst, seqTwoLast);
            listOfIndexes.add(indexToAdd);
        }
//        for (int i = 0; i <= listOfIndexes.size() - 1; i++){
//            if (listOfIndexes.get(i+1).firstIndexSecondSeq > )
//        }


    }

    public static void main(String args[]) throws IOException {
         MatchFinding MF = new MatchFinding();
         SuffixTree SF = new SuffixTree();
         String[] testerOne = {"D", "U", "N", "C", "A", "N"};
         String[] testerTwo = {"T", "R", "U", "O", "N", "G", "G"};

        String FS1 = new FastaSequence("seqs/TestOne.FASTA").getSequence();
        String FS2 = new FastaSequence("seqs/TestTwo.FASTA").getSequence();

        String[] FS1A = FS1.split("");
        String[] FS2A = FS2.split("");

        System.out.println(concatenateSequences(FS1A, FS2A).concat("$"));
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
//        System.out.println("Suffix Tree Test\n");
//        System.out.println("Enter string\n");
//        String str = br.readLine();
//        String str = concatenateSequences(testerOne, testerTwo);
//        String str = "GATTAGA$";
//        String str = "pqrpqpqabab$";
//        String str = "ABABABA$";
//        String str = "banana$";
//        String str = "GEEKSFORGEEKS$";
//        String str = "ATCGATCGA$";
//        String str = "ACTGGTAGATCAGGTA$";

//        String str = "ACTGTAACTGTAAAGCGATACTGATCACTGTCAGTGTGAAAAGTCATCATATGATAAAAGGTGACTACTAGTACTATAAAACT$";
//        String str = "ACTGTAACTGTAACT$";
        String str = concatenateSequences(FS1A, FS2A).concat("$");
//        String str = "ACTGTAACTGTAAAGCGATACTGATCACTGTCAGTGTGAAAAGTCATCATATGATAAAAGGTGACTACTAGTACTATAAAACT$";

        /** Construct Suffix Tree **/
        SuffixTree st = new SuffixTree();
        String longestAns = "";
        ArrayList<String> matchesArray = new ArrayList<>();
        st.FS1 = FS1;
        st.FS2 = FS2;
        st.T = str.toCharArray();
        st.N = st.T.length - 1;
        int x = 0;
        for (int i = 0 ; i <= st.N ; i++ )
            st.AddPrefix( st.active, i );
//        st.dump_edges( st.N );
        long startTime = System.currentTimeMillis();
        longestAns = st.subSequence_2();
        matchesArray = st.ListOfSubseqs;
        long endTime = System.currentTimeMillis();
        ArrayList<String> longerStringArray = new ArrayList<>();
        longerStringArray = returnLongerStrings(matchesArray, longestAns, st.FS1, st.FS2);
        ArrayList<String> reducedLongerStringArray = new ArrayList<>();
        reducedLongerStringArray = returnNonRepeatStrings(longerStringArray);
        System.out.println("TIME:" + (endTime - startTime) + "ms");
        System.out.println("longestAns is " + longestAns);
        System.out.println("shorter Array is " + returnLongerStrings(matchesArray, longestAns, st.FS1, st.FS2));
        System.out.println("shorter Array is " + returnLongerStrings(matchesArray, longestAns, st.FS1, st.FS2).size());
        System.out.println("non-repeat array is " + reducedLongerStringArray);
        alignAnchors(FS1, FS2, reducedLongerStringArray);
//        System.out.println("matchesArray is " + matchesArray.size());
        System.out.println(st.ListOfSubseqs.size());
    }

}
