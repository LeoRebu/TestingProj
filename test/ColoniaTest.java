import static org.junit.Assert.*;

import java.util.ArrayList;

import org.junit.Test;

public class ColoniaTest {
	
	Colonia colony;
	public ColoniaTest() {
		colony = new Colonia();
	}
	
	@Test
	public void testInit() {
		colony.setName("aa01");
		colony.setYobQueen(2017);
		colony.setQualQueen(5);
		colony.increaseTotalHoney(100);
		assertEquals("aa01",colony.getName());
		assertEquals(2017,colony.getYobQueen());
		assertEquals(5,colony.getQualQueen());
		assertEquals(100,colony.getTotalHoney());
		
		colony.setYobQueen(2013);
		colony.setQualQueen(7);
		
		assertEquals(2017,colony.getYobQueen());
		assertEquals(5,colony.getQualQueen());
	}

	
	@Test
	public void testStatementCov() {
		Colonia col = new Colonia();
		assertTrue(col.getTotalHoney()==0);
		col = new Colonia("aa02",2018,4,5,new ArrayList<Report>());
		
		col.addReport(new Report());
		
		assertNotNull(col.getReports());
	}

}
