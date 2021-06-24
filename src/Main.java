import java.util.ArrayList;
import java.util.Scanner;
import java.io.File;
import java.io.FileNotFoundException;

/**
* <h1>Main!</h1>
* Classe main per testare le classi colonia e report ed i metodi al loro interno
* <p>
* Giving proper comments in your program makes it more
* user friendly and it is assumed as a high quality code.
* 
*
* @author  Leonardo Rebucini
* @version 1.0
* @since   2021-06-6 
*/
public class Main {
	
	/*
	 * Metodo main per testare i metodi delle classi Colonia e Report
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		ArrayList<Colonia> listaColonie = new ArrayList<Colonia>();
		String nomeFile = "colonie.txt";
		//ArrayList<String> 
		importFile(nomeFile,listaColonie);

		 System.out.println(listaColonie.get(0).getName());
	}
	
	/*
	 * Metodo per importare i dati contenuti nel file passato per parametro, nella
	 * collezione di colonie passata.
	 * 
	 * Params:
	 *  nomeFile: stringa contenente la path del file di testo contenente le colonie
	 *  listColonie: collection dove inserire le colonie. Deve essere gia' inizializzata
	 */
	//@ requires listColonie!=null;
	public static void importFile (final String nomeFile, ArrayList<Colonia> listColonie) {
		try {
			final File myFile = new File(nomeFile);
			Scanner myReader = new Scanner(myFile);
		    final String delim = "[|]+";
			/*@ loop_invariant
			  @ myReader != null;*/
			while (myReader.hasNextLine()) {
			    String colony = myReader.nextLine();
			    String[] colonyData = colony.split(delim);
			    Colonia newCol = new Colonia();
			    newCol.setName(colonyData[0]);
			    newCol.setYobQueen(Integer.parseInt(colonyData[1]));
			    newCol.setQualQueen(Integer.parseInt(colonyData[2]));
			    newCol.increaseTotalHoney(Integer.parseInt(colonyData[3]));
			    
			    listColonie.add(newCol);
		    }
		    myReader.close();
		 } catch (FileNotFoundException e) {
			 // System.out.println("An error occurred.");
			 e.printStackTrace();
		 }
	}

}
