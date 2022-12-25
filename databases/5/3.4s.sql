select
	StudentId, StudentName, GroupId
from
	Lecturers
		natural join Marks
		natural join Plan
		natural join Students
where
	Mark = :Mark and LecturerName = :LecturerName;