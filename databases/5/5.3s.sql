select
	StudentName, CourseName
from
	( select distinct
		 Students.StudentId, Plan.CourseId
	 from
		 Students
			 natural join Plan
			 left join Marks on Students.StudentId = Marks.StudentId and Plan.CourseId = Marks.CourseId
	 where
		 Marks.Mark is null or Marks.Mark != 4 and Marks.Mark != 5
	) SidCid
	natural join Students
	natural join Courses;