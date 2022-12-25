select
    Students.StudentId, StudentName, GroupId
from
    Students
        left join (Marks natural join Courses) on Students.StudentId = Marks.StudentId and Courses.CourseName = :CourseName
where
    Marks.Mark is null;