select
	StudentId, CourseId
from
	Students, Plan
where
	Plan.GroupId = Students.GroupId
union select
	StudentId, CourseId
from
	Marks;