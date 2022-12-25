select
	StudentName, CourseName
from
	(select distinct StudentId, CourseId from Students natural join Plan) SidCid
	natural join Students
	natural join Courses;