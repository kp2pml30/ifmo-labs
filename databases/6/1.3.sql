select StudentId, StudentName, GroupId
from
	Students
where
	StudentId in (
		select Marks.StudentId
		from Marks
		where
			Mark = :Mark
			and CourseId = :CourseId
	);